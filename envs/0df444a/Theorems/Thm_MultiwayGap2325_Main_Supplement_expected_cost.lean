-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_expected_cost
-- name    : MultiwayGap2325.Main.Supplement.expected_cost
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:54:35.566269+00:00
-- url     : https://prove2.me/theorems/4ca07d7a-fe61-467d-8f5d-2b2df6fe3fc7
-- title:
--   Lemma 5.10 — Finite expected actual cost
-- statement:
--   The actual extended crossing cost $c(\xi)$ of a random non-opposite cut is almost-everywhere measurable and almost surely finite, has finite lower integral, and its real value is Bochner integrable. After splitting it into the sum of its face and terminal components almost surely, the approximation factor gives
--   $$
--   \mathbb E[c(C)]\le \alpha L,
--   $$
--   where $L$ is the fractional cost (7).
--
--   The interior bound uses the expected-crossing estimate of Lemma 5.6(ii)–(iii). For terminal facets, $d(y,e_i)=1-T$ gives $\Pr[C(y)\ne i]\le\alpha(1-T)$, and summing the two contributions yields $\alpha L$.
--
--   **Formalization Note** The split concerns the actual extended cost, not a separately assumed integrable surrogate. No positivity of $\alpha$ or $L$ and no regularity of individual cut interfaces is assumed.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Lemma 5.10, p.22; Lemma 5.6 and equation (17), pp.17–19.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

open MeasureTheory Filter
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- Lemma 5.10, p.22, with all measurability and finiteness obligations required
by the formal Theorem 3.4. -/
theorem MultiwayGap2325.Main.Supplement.expected_cost
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    let cost := fun ξ => cutCost T D.weighting (fun x => C.labeling (ξ, x))
    let A := fun ξ => totalRealFaceCost T D.weighting (fun x => C.labeling (ξ, x))
    let E := fun ξ => realTerminalCost T D.weighting (fun x => C.labeling (ξ, x))
    AEMeasurable cost P ∧
    (∀ᵐ ξ ∂P, cost ξ ≠ ⊤) ∧
    (∫⁻ ξ, cost ξ ∂P) ≠ ⊤ ∧
    Integrable (fun ξ => (cost ξ).toReal) P ∧
    Integrable E P ∧
    (∀ᵐ ξ ∂P, (cost ξ).toReal = A ξ + E ξ) ∧
    (∫ ξ, (cost ξ).toReal ∂P) ≤ α * totalL T D.weighting := by sorry
