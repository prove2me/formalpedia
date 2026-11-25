-- Prove2me | Theorems.Thm_GlobalTheory_T_conjugate_self_reciprocal_charpoly
-- name    : GlobalTheory.T.conjugate_self_reciprocal_charpoly
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:19.014484+00:00
-- url     : https://prove2.me/theorems/6adb8793-74ae-4833-8414-f3ef7194df57
-- title:
--   T: conjugate self reciprocal charpoly
-- statement:
--   The T construction uses the conjugate self reciprocal charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/IsobaricBaseChange/IntegralCoefficientBaseChange/UnitaryBaseChangeCharacters/UnitaryBaseChangeLinks/ConjugateSelfReciprocalCharpoly.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/IsobaricBaseChange/IntegralCoefficientBaseChange/UnitaryBaseChangeCharacters/UnitaryBaseChangeLinks/ConjugateSelfReciprocalCharpoly.lean#L9-L10

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjugateSelfReciprocalCharpoly
import Mathlib
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_ConjugateSelfReciprocalCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG

theorem GlobalTheory.T.conjugate_self_reciprocal_charpoly : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ) (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by sorry
