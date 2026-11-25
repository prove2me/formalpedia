-- Prove2me | Theorems.Thm_GlobalTheory_HL_LocCongApprox_bc_sub
-- name    : GlobalTheory.HL.LocCongApprox.bc_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:43:28.800795+00:00
-- url     : https://prove2.me/theorems/b648c66e-9929-481b-9baa-ce9c611b51de
-- title:
--   Loc Cong Approx: bc sub
-- statement:
--   The Loc Cong Approx construction uses the bc sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsGlobalUnitriangularOfLocalCongruence.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsGlobalUnitriangularOfLocalCongruence.lean#L69-L70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGlobalUnitriangularOfLocalCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocCongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
variable (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}

theorem GlobalTheory.HL.LocCongApprox.bc_sub (u v : Fin N → E) : A.bc p (u - v) = A.bc p u - A.bc p v := by sorry
