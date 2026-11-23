-- Prove2me | Theorems.Thm_MassDataIdxCore_firstSplit_apply
-- name    : MassDataIdxCore.firstSplit_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:10.391531+00:00
-- url     : https://prove2.me/theorems/648ba2bf-8b6a-44cd-ac3d-bb5d7e3aeb0d
-- title:
--   Mass Data Idx Core: first Split apply
-- statement:
--   The Mass Data Idx Core construction uses the first Split apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/StRedCore.lean#L16-L16

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K)

theorem MassDataIdxCore.firstSplit_apply (t : T) : t1 θ t = (θ t).1 := by sorry
