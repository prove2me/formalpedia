-- Prove2me | Theorems.Thm_MainStatements_BetaInf_sN_nonneg
-- name    : MainStatements.BetaInf.sN_nonneg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:11.774263+00:00
-- url     : https://prove2.me/theorems/87d27052-6465-4614-bd99-e8fee56b1930
-- title:
--   Beta Inf: s N nonneg
-- statement:
--   The Beta Inf construction uses the s N nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/KFiniteVectors/KDecay.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/KFiniteVectors/KDecay.lean#L16-L17

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_CompanionTheory_AutomorphicTheory_KFiniteVectors_KDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MainStatements MainStatements.BetaInf
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace
noncomputable section

theorem MainStatements.BetaInf.sN_nonneg {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ sN g := by sorry
