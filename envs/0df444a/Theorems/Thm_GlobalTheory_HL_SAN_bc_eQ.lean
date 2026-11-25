-- Prove2me | Theorems.Thm_GlobalTheory_HL_SAN_bc_eQ
-- name    : GlobalTheory.HL.SAN.bc_eQ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:33.300324+00:00
-- url     : https://prove2.me/theorems/0e0058aa-ff6f-5a8b-9b33-6d67c6d9e355
-- title:
--   SAN: bc e Q
-- statement:
--   The SAN construction uses the bc e Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemCoord.lean#L142-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemCoord.lean#L142-L153

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.SAN.bc_eQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (x u : Fin N → E) (s : E) (v : Fin N → E) :
    A.bc p (_root_.GlobalTheory.HL.SAN.eQ sig Hm x u s v) =
      _root_.GlobalTheory.HL.eich (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p u) ((A.loc p).ιE s) (A.bc p v) := by sorry
