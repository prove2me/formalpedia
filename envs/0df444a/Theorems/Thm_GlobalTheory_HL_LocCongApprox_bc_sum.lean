-- Prove2me | Theorems.Thm_GlobalTheory_HL_LocCongApprox_bc_sum
-- name    : GlobalTheory.HL.LocCongApprox.bc_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:35:25.559217+00:00
-- url     : https://prove2.me/theorems/3a40ef4f-bf3a-5380-bf03-154c6cdec0a1
-- title:
--   Loc Cong Approx: bc sum
-- statement:
--   The Loc Cong Approx construction uses the bc sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsGlobalUnitriangularOfLocalCongruence.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsGlobalUnitriangularOfLocalCongruence.lean#L75-L77

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

theorem GlobalTheory.HL.LocCongApprox.bc_sum {ι : Type} (s : Finset ι) (f : ι → Fin N → E) :
    A.bc p (∑ i ∈ s, f i) = ∑ i ∈ s, A.bc p (f i) := by sorry
