-- Prove2me | Theorems.Thm_GlobalTheory_HaarLatticeScale_lt_one_iff_le_exp
-- name    : GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:52:28.145907+00:00
-- url     : https://prove2.me/theorems/43bbf303-ba18-4367-9887-8ca1ae473a53
-- title:
--   Haar Lattice Scale: lt one iff le exp
-- statement:
--   The Haar Lattice Scale construction uses the lt one iff le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureRealValuedLeExp.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureRealValuedLeExp.lean#L16-L21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsResidueEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureRealValuedLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HaarLatticeScale

theorem GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp (t : WithZero (Multiplicative ℤ)) :
    t < 1 ↔ t ≤ WithZero.exp (-1 : ℤ) := by sorry
