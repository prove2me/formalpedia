-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_one_face
-- name    : MultiwayGap2325.Main.Supplement.one_face
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:53:46.268071+00:00
-- url     : https://prove2.me/theorems/82802d4c-9969-4dc0-b3b1-a900638b7221
-- title:
--   Lemma 5.9 — One-face flux versus cost, with integrability
-- statement:
--   For every face $S$, the expected selected flux jump and the expected interior crossing cost are well-defined real integrals, and
--   $$
--   \mathbb E[\Lambda_S(C)]\le \mathbb E[\operatorname{cost}_S(C)].
--   $$
--
--   The almost-sure finite-variation structure gives an interface with exactly two neighboring labels. The boundary-flux identity expresses $\mathbb E[\Lambda_S(C)]$ by the normal difference of the two selected flows, while the cut condition bounds that difference by the weighted directional crossing densities. Cell walls carry no crossing mass almost surely.
--
--   **Formalization Note** The two integrability conclusions make the finite sums and exchanges with expectation in Theorem 3.4 legitimate; they are consequences of bounded flows and finite expected crossing costs, not extra hypotheses on the cut.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Lemma 5.9, p.22; prerequisites Lemma 5.6, Fact 5.7 and Lemma 5.8, pp.17–21.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

open MeasureTheory Filter
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- Lemma 5.9, p.22, together with the integrability needed to take finite sums
of its expectations. Neither assertion is an additional geometric restriction. -/
theorem MultiwayGap2325.Main.Supplement.one_face
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    (∀ S : Face q,
      Integrable (fun ξ => fluxJump T D S (fun x => C.labeling (ξ, x))) P) ∧
    (∀ S : Face q,
      Integrable (fun ξ => realFaceCost T D.weighting S (fun x => C.labeling (ξ, x))) P) ∧
    ∀ S : Face q,
      (∫ ξ, fluxJump T D S (fun x => C.labeling (ξ, x)) ∂P) ≤
        ∫ ξ, realFaceCost T D.weighting S (fun x => C.labeling (ξ, x)) ∂P := by sorry
