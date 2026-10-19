-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_selections_variance
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.selections_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:31:09.91948+00:00
-- url     : https://prove2.me/theorems/29861ea2-88ee-4542-acf9-3878d02a5684
-- title:
--   Variance bound for averaged coordinate-selection events with few collisions
-- statement:
--   For a nonempty finite set $X$ and $h:X\to\mathbb R$ write $\operatorname{avg}_{x\in X}h(x)=\frac1{|X|}\sum_{x\in X}h(x)$.
--
--   Let $\kappa$, $A$, $J$, $Y$ be finite sets with $A$ and $Y$ nonempty, and let $\omega$ range over all maps $\kappa\to A$ (uniformly random assignments of a symbol in $A$ to each coordinate). Suppose we are given functions $f_j(y,\omega)\in[0,1]$ for $j\in J$, $y\in Y$, $\omega\in A^{\kappa}$, coordinate maps $c:Y\times J\to\kappa$, target symbols $a:Y\times J\to A$, a set $G\subseteq Y$ of good indices, and real numbers $b,d$, such that
--
--   1. for every $y\in G$ the map $j\mapsto c(y,j)$ is injective and $f_j(y,\omega)=\mathbf 1\big[\omega(c(y,j))=a(y,j)\big]$ for all $j$ and $\omega$;
--   2. the proportion of bad indices is at most $b$: $|Y\setminus G|/|Y|\le b$;
--   3. the proportion of ordered pairs $(y,y')\in Y\times Y$ that share a coordinate, i.e. with $c(y,j)=c(y',l)$ for some $j,l\in J$, is at most $d$.
--
--   Then
--
--   $$
--   \operatorname{avg}_{\omega\in A^{\kappa}}\Big(\operatorname{avg}_{y\in Y}\prod_{j\in J}f_j(y,\omega)-|A|^{-|J|}\Big)^2\le 3\,(2b+d).
--   $$
--
--   For a good index $y$ the product $\prod_jf_j(y,\omega)$ is the indicator that $|J|$ distinct coordinates of $\omega$ take prescribed values, an event of probability $|A|^{-|J|}$. The theorem says that the empirical frequency of these events over $y\in Y$ concentrates around $|A|^{-|J|}$, as long as few indices are degenerate and few pairs share coordinates; dependence is charged only to such collisions. It is the moment estimate behind the regularity of the random slot hypergraph.
--
--   **Formalization Note** The averaged variable is `ω : κ → A`; `good` is a decidable predicate, and both proportions are written as averages of indicator functions over $Y$ and over $Y\times Y$. The pairs in hypothesis 3 are ordered and include the diagonal pairs $(y,y)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/DependentMoments.lean#L104-L142

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
variable {κ : Type uκ} {A : Type uA} {J : Type uJ} {Y : Type uY} [Fintype κ] [DecidableEq κ] [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype J] [Fintype Y] [Nonempty Y]

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.selections_variance (f : J → Y → (κ → A) → ℝ)
    (c : Y → J → κ) (a : Y → J → A) (good : Y → Prop)
    [DecidablePred good] {b d : ℝ}
    (hf : ∀ j y ω, 0≤f j y ω ∧ f j y ω≤1)
    (hc : ∀ y, good y → Function.Injective (c y))
    (ha : ∀ y, good y → ∀ j ω,
      f j y ω=(if ω (c y j)=a y j then 1 else 0))
    (hb : avg (fun y ↦ if good y then 0 else 1)≤b)
    (hd : avg (fun yy : Y × Y ↦
      if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0)≤d) :
    avg (fun ω : κ → A ↦
      (avg (fun y ↦ ∏ j, f j y ω)-(1/(Fintype.card A : ℝ))^(Fintype.card J))^2)
        ≤ 3*(2*b+d) := by sorry
