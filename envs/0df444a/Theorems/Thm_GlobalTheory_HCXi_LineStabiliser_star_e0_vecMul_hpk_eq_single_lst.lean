-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_star_e0_vecMul_hpk_eq_single_lst
-- name    : GlobalTheory.HCXi.LineStabiliser.star_e0_vecMul_hpk_eq_single_lst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:17.840773+00:00
-- url     : https://prove2.me/theorems/b5484eb0-f7eb-57a3-a500-3cbb447a04ba
-- title:
--   Line Stabiliser: star e0 vec Mul hpk eq single lst
-- statement:
--   The Line Stabiliser construction uses the star e0 vec Mul hpk eq single lst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L29-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)

theorem GlobalTheory.HCXi.LineStabiliser.star_e0_vecMul_hpk_eq_single_lst : star (e0 k r') ᵥ* Hpk k (1 + r') = Pi.single (lst k r') 1 := by sorry
