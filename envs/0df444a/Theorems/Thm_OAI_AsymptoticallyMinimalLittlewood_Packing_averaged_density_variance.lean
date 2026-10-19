-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_averaged_density_variance
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.averaged_density_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:33:10.432687+00:00
-- url     : https://prove2.me/theorems/3b9c2484-d9ca-42d9-bac4-93431a1b0655
-- title:
--   Averaged second-moment bound for joint hit densities on the fibers of a linear form
-- statement:
--   Let $K$ be a finite field and $V$ a finite vector space over $K$. For a finite set $X$ and $F:X\to\mathbb{R}$ write $\operatorname{avg}_{x\in X}F(x)=\frac{1}{|X|}\sum_{x\in X}F(x)$ for the uniform average. Let $J$ be a finite index set (the *rows*), $\kappa$ a finite set (the *chunks*) and $A$ a finite nonempty set (the *alphabet*). A *configuration* is a map $\omega:\kappa\to A$; the set of all configurations is $A^\kappa$.
--
--   The data are: linear forms $f:V\to K$ and $g_j:V\to K$ for $j\in J$; finite sets $G,S\subseteq K$; a map $c:K\to\kappa$ assigning a chunk to each value; a predicate $\mathrm{hit}_j(t,\omega)$ for $j\in J$, $t\in K$, $\omega\in A^\kappa$; and a real number $B$. Assume:
--
--   1. $f$ is surjective, every $g_j$ is surjective, the pair map $(f,g_j):V\to K^2$ is surjective for every $j$, and $(g_j,g_l):V\to K^2$ is surjective for all $j\neq l$;
--   2. any two values $t,u\in G$ with $c(t)=c(u)$ satisfy $t+u\in S$ or $t-u\in S$;
--   3. for every $j\in J$ and every $t\in G$ there is a letter $a\in A$ such that, for all configurations $\omega$, $\mathrm{hit}_j(t,\omega)$ holds if and only if $\omega(c(t))=a$;
--   4. every chunk class is small: $|\{t\in K: c(t)=k\}|\le B$ for every $k\in\kappa$.
--
--   For $s\in K$ let $f^{-1}(s)=\{y\in V: f(y)=s\}$ and let
--   $$X_s(\omega)=\operatorname{avg}_{y\in f^{-1}(s)}\ \prod_{j\in J}\mathbf 1\big[\mathrm{hit}_j(g_j(y),\omega)\big]$$
--   be the proportion of points of the hyperplane $\{f=s\}$ all of whose coordinates $g_j(y)$ are hit. Then
--   $$\operatorname{avg}_{\omega\in A^\kappa}\ \operatorname{avg}_{s\in K}\Big(X_s(\omega)-|A|^{-|J|}\Big)^2\ \le\ 3\left(2\left(\frac{|J|\,(|K|-|G|)}{|K|}+\frac{2\,|J|^2\,|S|}{|K|}\right)+\frac{|J|^2\,B}{|K|}\right).$$
--
--   If the chunks $c(g_j(y))$, $j\in J$, were distinct and $\omega$ uniformly random, the product would equal $1$ with probability exactly $|A|^{-|J|}$. The theorem says that, on average over the anchor value $s$, the hit density on the fiber $\{f=s\}$ concentrates around this value in mean square, with an error controlled by the proportion of values outside $G$, the size of the collision set $S$ and the chunk size $B$. In the construction of flat Littlewood polynomials it is the abstract variance estimate behind the degree concentration of the random slot hypergraph, before atypical vertices are pruned.
--
--   **Formalization Note** Averages are the uniform averages `avg` over finite types; the inner average runs over the subtype `fiber f s`. The quantity $|K|-|G|$ is a subtraction of real numbers. Surjectivity of each $g_j$ is a separate hypothesis even though it follows from surjectivity of $(f,g_j)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/DependentMoments.lean#L397-L446

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uκ uA uJ uY uV uK uΩ uI
open scoped BigOperators
open Finset
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} {A : Type uA} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Nonempty A] [DecidableEq A]

omit [DecidableEq V] in
theorem OAI.AsymptoticallyMinimalLittlewood.Packing.averaged_density_variance (f : V →ₗ[K] K) (g : J → V →ₗ[K] K)
    (hf : Function.Surjective f)
    (hg : ∀ j, Function.Surjective (g j))
    (hfg : ∀ j, Function.Surjective (f.prod (g j)))
    (hpair : ∀ j l, j≠l → Function.Surjective ((g j).prod (g l)))
    (G S : Finset K) (chunk : K → κ)
    (hchunk : ∀ t∈G, ∀ u∈G, chunk t=chunk u → t+u∈S ∨ t-u∈S)
    (hit : J → K → (κ → A) → Prop) [∀ j t ω, Decidable (hit j t ω)]
    (hhit : ∀ j t, t∈G → ∃ a : A, ∀ ω, hit j t ω ↔ ω (chunk t)=a)
    {B : ℝ} (hB : ∀ k, ((Finset.univ.filter (fun t : K ↦ chunk t=k)).card : ℝ)≤B) :
    avg (fun ω : κ → A ↦ avg (fun s : K ↦
      (avg (fun y : fiber f s ↦ ∏ j, if hit j (g j y) ω then (1 : ℝ) else 0)-
        (1/(Fintype.card A : ℝ))^(Fintype.card J))^2)) ≤
      3*(2*((Fintype.card J : ℝ)*(Fintype.card K-G.card)/Fintype.card K+
          2*(Fintype.card J : ℝ)^2*S.card/Fintype.card K)+
        (Fintype.card J : ℝ)^2*B/Fintype.card K) := by sorry
