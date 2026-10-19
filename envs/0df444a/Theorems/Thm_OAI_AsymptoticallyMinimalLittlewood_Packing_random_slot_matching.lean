-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_random_slot_matching
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.random_slot_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:35:06.301547+00:00
-- url     : https://prove2.me/theorems/6a0456ea-6be8-4d53-967b-c97dca078068
-- title:
--   Almost-perfect matchings in random slot hypergraphs over a finite field
-- statement:
--   Fix a finite nonempty index set $I$ (the *rows*), a real number $K_0\ge0$ and a real number $\eta$ with $0<\eta\le1$. For a finite set $X$ write $\operatorname{avg}_{x\in X}F(x)=\frac{1}{|X|}\sum_{x\in X}F(x)$.
--
--   **Slot hypergraphs.** Let $\mathbb{K}$ be a finite field, $V$ a finite vector space over $\mathbb{K}$, $(g_i)_{i\in I}$ a family of linear forms $g_i:V\to\mathbb{K}$, $\Omega$ a finite nonempty set of *configurations*, and $\mathrm{hit}(i,t,\omega)$ a predicate for $i\in I$, $t\in\mathbb{K}$, $\omega\in\Omega$. For each $\omega\in\Omega$:
--   - the *vertices* are $U_\omega=\{(i,t)\in I\times\mathbb{K}:\ \mathrm{hit}(i,t,\omega)\}$;
--   - the *edges* are the points of $E_\omega=\{y\in V:\ \mathrm{hit}(i,g_i(y),\omega)\text{ for all }i\in I\}$, and the edge $y$ has *support* $\sigma(y)=\{(i,g_i(y)):\ i\in I\}$, a set of $|I|$ vertices;
--   - the *slot density* of $(i,s)\in I\times\mathbb{K}$ is
--   $$\rho^\omega_i(s)=\operatorname{avg}_{y\in V,\ g_i(y)=s}\ \prod_{j\neq i}\mathbf 1\big[\mathrm{hit}(j,g_j(y),\omega)\big].$$
--
--   **Statement.** There exist constants $e>0$ and $T>0$, depending only on $I$, $K_0$ and $\eta$, with the following property. Let $\mathbb{K},V,\Omega,(g_i),\mathrm{hit}$ be as above, let $p,a,b,n\in\mathbb{R}$, and put
--   $$D=\frac{|V|}{|\mathbb{K}|}\,p,\qquad C=\frac{|V|}{|\mathbb{K}|^2}.$$
--   Assume
--   1. every $g_i$ is surjective, and $(g_i,g_j):V\to\mathbb{K}^2$ is surjective for all $i\neq j$;
--   2. $p>0$ and $b\ge0$;
--   3. $\operatorname{avg}_{\omega\in\Omega}\operatorname{avg}_{s\in\mathbb{K}}\big(\rho^\omega_i(s)-p\big)^2\le a$ for every $i\in I$;
--   4. $|I|\,|\mathbb{K}|\,a/(ep/2)^2\le b$;
--   5. $|U_\omega|=n$ for every $\omega\in\Omega$;
--   6. $T\le D$, $T\le n-b$, $C\le eD$, $nC\le K_0D$ and $bC\le eD/2$.
--
--   Then there exist a configuration $\omega\in\Omega$ and a set $M\subseteq E_\omega$ of edges with pairwise disjoint supports such that
--   $$(1-\eta)(n-b)\ \le\ |I|\cdot|M| .$$
--
--   Since a matching $M$ covers exactly $|I|\,|M|$ vertices, the conclusion says that for a suitable configuration the slot hypergraph has a matching covering all of its $n$ vertices except roughly a proportion $\eta$ and an exceptional budget $b$. Here $D$ is the typical vertex degree and $C$ the maximal codegree of the slot hypergraph. This is the step of the signed-slot packing where a mean-square bound on slot densities is turned into an actual large matching.
--
--   **Formalization Note** The types $\mathbb{K}$, $V$, $\Omega$ and $I$ live in `Type` (universe $0$), and $e,T$ are chosen before $\mathbb{K},V,\Omega$ are quantified, so the constants are uniform over all such data. The slot density is `slotDensity`, an average over the subtype `fiber (g i) s` of a product over the subtype of indices $j\neq i$; $U_\omega$, $E_\omega$ and $\sigma$ are `slotVertices`, `slotEdges` and `slotSupport`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotGraph.lean#L185-L245

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
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uI uK uV uJ
open scoped BigOperators
open Finset Nibble
variable {I : Type} [Fintype I] [DecidableEq I]

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.random_slot_matching (hr : 1≤Fintype.card I) {K₀ η : ℝ}
    (hK₀ : 0≤K₀) (hη : 0<η) (hη₁ : η≤1) :
    ∃ e T : ℝ, 0<e ∧ 0<T ∧
    ∀ {K V Ω : Type} [Field K] [Fintype K] [DecidableEq K]
      [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V] [Fintype Ω] [Nonempty Ω],
    ∀ (g : I → V →ₗ[K] K) (hit : I → K → Ω → Prop)
      [∀ i s ω, Decidable (hit i s ω)] (p a b n : ℝ),
      (∀ i, Function.Surjective (g i)) →
      (∀ i j, i≠j → Function.Surjective ((g i).prod (g j))) →
      0<p → 0≤b →
      (∀ i, avg (fun ω ↦ avg (fun s ↦ (slotDensity g (fun j t ↦ hit j t ω) i s-p)^2))≤a) →
      Fintype.card I*Fintype.card K*a/(e*p/2)^2≤b →
      (∀ ω, ((slotVertices (fun i t ↦ hit i t ω)).card : ℝ)=n) →
      T≤(Fintype.card V/(Fintype.card K : ℝ))*p → T≤n-b →
      Fintype.card V/(Fintype.card K : ℝ)^2≤e*((Fintype.card V/(Fintype.card K : ℝ))*p) →
      n*(Fintype.card V/(Fintype.card K : ℝ)^2)≤K₀*((Fintype.card V/(Fintype.card K : ℝ))*p) →
      b*(Fintype.card V/(Fintype.card K : ℝ)^2)≤e*((Fintype.card V/(Fintype.card K : ℝ))*p)/2 →
      ∃ ω, ∃ M⊆slotEdges g (fun i t ↦ hit i t ω),
        (M : Set V).Pairwise (fun y z ↦ Disjoint (slotSupport g y) (slotSupport g z)) ∧
        (1-η)*(n-b)≤Fintype.card I*(M.card : ℝ) := by sorry
