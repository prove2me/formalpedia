-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_flux_terminal_identity
-- name    : MultiwayGap2325.Main.Supplement.flux_terminal_identity
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:09:12.223028+00:00
-- url     : https://prove2.me/theorems/86158002-f38a-4ab2-be28-5a40e252a5b8
-- title:
--   Lemma 5.2 — The summation identity (15)
-- statement:
--   For every realization of the cut, regrouping the selected terminal and coordinate-facet fluxes by their common child face gives
--   $$
--   \sum_S\Lambda_S(C)+\operatorname{cost}_{\mathrm{term}}(C)
--   =B+\sum_{U:\,|U|\ge2}\int_{\Omega_U}
--   \left(b_{C(x)}(x)-\operatorname{div}F_{C(x)}(x)\right)dx.
--   $$
--   The selected terminal flux and terminal cost combine to $B$ on terminal facets. The parent’s outward coordinate flux is the negative incoming supply at the same point, with the same measure and the same actual cut label. On an interval the coordinate-facet sum is empty.
--
--   **Formalization Note** The equality uses the matched measures and the original pointwise labels. Its proof must also establish that the bounded terminal extended cost has the corresponding real integral expression.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Lemma 5.2 and equation (15), p.14; sign conventions (12)–(13), p.12.

import Definitions.Def_MultiwayGap2325_Main_Supplement_ConservationDefects

open MeasureTheory Filter Set
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- Equation (15), p.14: the algebraic rearrangement of all selected boundary
and interior terms. -/
theorem MultiwayGap2325.Main.Supplement.flux_terminal_identity
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (ξ : Ξ) :
    totalFluxJump T D (fun x => C.labeling (ξ, x)) +
        realTerminalCost T D.weighting (fun x => C.labeling (ξ, x)) =
      totalB T D.weighting +
        totalConservationDefect T D (fun x => C.labeling (ξ, x)) := by sorry
