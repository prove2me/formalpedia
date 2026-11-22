-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_selected_conservation_bound
-- name    : MultiwayGap2325.Main.Supplement.selected_conservation_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:11:12.875931+00:00
-- url     : https://prove2.me/theorems/f5565d94-5ea8-4e1a-bf86-eb41aede7512
-- title:
--   Lemma 5.2 — Selected conservation on one face
-- statement:
--   On every face $S$ and for every realization of a non-opposite cut,
--   $$
--   -\int_{\Omega_S}\epsilon_S(x)\,dx
--   \le \int_{\Omega_S}\left(b_{C(x)}(x)-\operatorname{div}F_{C(x)}(x)\right)dx.
--   $$
--   Indeed, $C(x)$ is an allowed label of $S$, so the conservation inequality applies almost everywhere to that selected label.
--
--   **Formalization Note** The statement concerns the integrated real quantities used in (15), including the measure-theoretic justification for integrating the selected almost-everywhere inequality.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), final paragraph of the proof of Lemma 5.2, p.14.

import Definitions.Def_MultiwayGap2325_Main_Supplement_ConservationDefects

open MeasureTheory Filter Set
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal
universe u

/-- The final inequality in the proof of Lemma 5.2, p.14. -/
theorem MultiwayGap2325.Main.Supplement.selected_conservation_bound
    (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D)
    (Ξ : Type u) [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (ξ : Ξ) (S : Face q) :
    -(∫ x, D.allowance S x ∂faceVolume T S) ≤
      conservationDefect T D S (fun x => C.labeling (ξ, x)) := by sorry
