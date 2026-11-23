-- Prove2me | Theorems.Thm_GlobalTheory_PlaneTheta_exists_pos_le_of_summable
-- name    : GlobalTheory.PlaneTheta.exists_pos_le_of_summable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:21.241641+00:00
-- url     : https://prove2.me/theorems/c4514f3b-0589-41b0-b3ee-bf604d1cd841
-- title:
--   Plane Theta: exists pos le of summable
-- statement:
--   The Plane Theta construction uses the exists pos le of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L10-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta

theorem GlobalTheory.PlaneTheta.exists_pos_le_of_summable {ι : Type*} {q : ι → ℝ}
    (h : Summable fun i => Real.exp (-q i)) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, 0 < q i → δ ≤ q i := by sorry
