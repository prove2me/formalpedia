-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_cell_flow_integrable
-- name    : MultiwayGap2325.Main.Supplement.cell_flow_integrable
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:53:46.75577+00:00
-- url     : https://prove2.me/theorems/a15ddcb8-e6ec-4051-8a1b-041faba4745f
-- title:
--   Lemma 5.2 support — Integrability of a cell flow
-- statement:
--   Let $D$ be a valid flow instance, let $P$ be one of its cells on face $S$, and let $\ell$ be an allowed label on $S$. The vector field $D.field_{S,P,\ell}$ is Bochner integrable on $P$ with respect to the truncated face-volume measure $d\Omega_S$. This is the basic integrability fact needed when the selected field is decomposed into constant-label cells in Lemma 5.2.
-- source:
--   STOC 2027 submission #697, §5.1 cellwise flow definition and regularity (pp.11–12), used in the proof of Lemma 5.2 (p.14). Regularity makes each cell flow continuous on its compact cell; face volume has finite measure on compact subsets.

import Definitions.Def_MultiwayGap2325_Main_Supplement_Flows

open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement

theorem MultiwayGap2325.Main.Supplement.cell_flow_integrable
    (q : ℕ) (T : ℝ) (D : FlowData q) (S : Face q)
    (hD : IsFlowInstance T D) (P : Set (Vec q))
    (hP : P ∈ D.weighting.cells S) (l : CutLabel q) (hl : Allowed S l) :
    MeasureTheory.IntegrableOn (D.field S P l) P (faceVolume T S) := by sorry
