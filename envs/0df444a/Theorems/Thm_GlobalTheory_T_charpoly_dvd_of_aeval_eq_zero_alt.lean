-- Prove2me | Theorems.Thm_GlobalTheory_T_charpoly_dvd_of_aeval_eq_zero_alt
-- name    : GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:31:45.288435+00:00
-- url     : https://prove2.me/theorems/f282785e-21c4-5220-a578-fc53c7bb30ba
-- title:
--   T: charpoly dvd of aeval eq zero alt
-- statement:
--   The T construction uses the charpoly dvd of aeval eq zero alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/IsobaricBaseChange/IntegralCoefficientBaseChange/UnitaryBaseChangeCharacters/UnitaryBaseChangeLinks/CharpolyDvdOfAevalEqZero.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/IsobaricBaseChange/IntegralCoefficientBaseChange/UnitaryBaseChangeCharacters/UnitaryBaseChangeLinks/CharpolyDvdOfAevalEqZero.lean#L9-L10

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyDvdOfAevalEqZero
import Mathlib
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_CharpolyDvdOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG

theorem GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt : ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]), M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by sorry
