-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_flow_lower_bound
-- name    : MultiwayGap2325.Main.Supplement.flow_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:22:36.778014+00:00
-- url     : https://prove2.me/theorems/f6984d28-c409-4dfd-bda9-699e02eab810
-- title:
--   Theorem 3.4 — Flow lower bound
-- statement:
--   Fix an integer $q\ge2$, a real threshold $1/2<T<1$, and any valid flow instance on the full real simplex $\Delta_q$. Let $B$ be its total terminal-edge mass, $R$ its integrated allowance, and $L>0$ its fractional cost. On any probability space let $C$ be a jointly measurable random non-opposite cut with approximation factor $\alpha\in\mathbb R$.
--
--   Its actual extended crossing cost is almost surely finite, has finite nonnegative expectation, and its real value is integrable. With that expectation,
--
--   $$B-R\le\mathbb E[\operatorname{cost}(C)]\le\alpha L.$$
--
--   Consequently,
--
--   $$\alpha\ge\frac{B-R}{L},\qquad
--   \exists g\in\mathbb R:\quad G_k\longrightarrow g\quad\text{and}\quad g\ge\frac{B-R}{L}.$$
--
--   The bound holds for every valid flow instance and every such random cut. No positivity of $B-R$, normalization of $L$, finite support of the law, or regularity of the cut regions is assumed. This is the general certificate theorem connecting continuous flows to the existing finite CKR gap sequence.
--
--   **Formalization Note** Geometry, cells, densities, fields and allowances are fixed before the probability space and cut. Normal continuity permits tangential jumps. The expectation uses the actual boundary labels and essential interior crossing counts.
--
--   Differences from the source:
--   - encoding: faces and coordinate labels in [q] → Fin q labels and all faces with cardinality at least two; reason: the same finite coordinates and full real domains are represented, including intervals
--   - encoding: the expected actual cost in the theorem and its proof → extended nonnegative cost, with measurability, almost-sure finiteness, finite lower integral and real integrability asserted as conclusions; reason: this makes the source expectation meaningful without a totalized nonintegrable Bochner integral
--   - encoding: limiting gap inequality → a real limit g with Tendsto of the published gapSequence and the same bound; reason: the stated limit is explicit; no sign restriction on B minus R is introduced
--   - encoding: cellwise formulas on closed cells with normal continuity and the regularity of §5.1 → explicit cell formulas for C1 fields and continuous weight extensions, with actual Borel weight values used in cost; reason: the source permits tangential jumps and arbitrary wall values; no global smoothness or intercell weight continuity is imposed
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 3.4, p. 7

import Definitions.Def_MultiwayGap2325_Main_Supplement_Flows
import Definitions.Def_MultiwayGap2325_Main_Supplement_CrossingCost

open MeasureTheory Filter
universe u

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 3.4, pp.7–8, with the precise definitions of §5.1 and Definition 5.4.
Finiteness and integrability of the actual extended cost are conclusions, not restrictions on cuts. -/
theorem flow_lower_bound (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D) (hL : 0 < totalL T D.weighting)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    let cost := fun ξ => cutCost T D.weighting (fun x => C.labeling (ξ, x))
    AEMeasurable cost P ∧
    (∀ᵐ ξ ∂P, cost ξ ≠ ⊤) ∧
    (∫⁻ ξ, cost ξ ∂P) ≠ ⊤ ∧
    Integrable (fun ξ => (cost ξ).toReal) P ∧
    totalB T D.weighting - totalR T D ≤ ∫ ξ, (cost ξ).toReal ∂P ∧
    (∫ ξ, (cost ξ).toReal ∂P) ≤ α * totalL T D.weighting ∧
    (totalB T D.weighting - totalR T D) / totalL T D.weighting ≤ α ∧
    ∃ g : ℝ, Tendsto gapSequence atTop (nhds g) ∧
      (totalB T D.weighting - totalR T D) / totalL T D.weighting ≤ g := by sorry

end MultiwayGap2325.Main.Supplement
