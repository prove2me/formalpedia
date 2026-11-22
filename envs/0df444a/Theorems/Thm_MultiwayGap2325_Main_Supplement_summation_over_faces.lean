-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_summation_over_faces
-- name    : MultiwayGap2325.Main.Supplement.summation_over_faces
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:52:48.938819+00:00
-- url     : https://prove2.me/theorems/0d0f8d60-0317-4919-b17c-9872ef3c2b78
-- title:
--   Lemma 5.2 — Summation over faces
-- statement:
--   Fix a valid flow instance and one realization $c=C(\xi,\cdot)$ of a random non-opposite cut. With the selected flux jumps $\Lambda_S(c)$ of equation (10), the total terminal mass $B$, and the total allowance $R$, every realization satisfies
--   $$
--   B-R\le \sum_{S:\,|S|\ge2}\Lambda_S(c)+\operatorname{cost}_{\mathrm{term}}(c).
--   $$
--
--   Terminal flux and terminal cost add to the terminal density on every terminal facet. On a coordinate facet, non-oppositeness makes the selected label an allowed label of the child face, and conservation bounds the supply-minus-divergence integrand below by the negative allowance. This is the deterministic step of the flow lower bound.
--
--   **Formalization Note** The flux-jump and real terminal-cost functions use the matched face measures and the original pointwise boundary labels; no positivity of $B-R$ is assumed.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Lemma 5.2 and equation (15), p.14.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps

open MeasureTheory Filter
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- Lemma 5.2, p.14. The actual boundary labels are used, and the real terminal
cost is finite by the bounded terminal densities and finite facet measures. -/
theorem MultiwayGap2325.Main.Supplement.summation_over_faces
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (ξ : Ξ) :
    totalB T D.weighting - totalR T D ≤
      totalFluxJump T D (fun x => C.labeling (ξ, x)) +
        realTerminalCost T D.weighting (fun x => C.labeling (ξ, x)) := by sorry
