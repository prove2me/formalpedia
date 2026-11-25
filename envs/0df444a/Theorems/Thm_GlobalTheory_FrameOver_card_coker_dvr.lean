-- Prove2me | Theorems.Thm_GlobalTheory_FrameOver_card_coker_dvr
-- name    : GlobalTheory.FrameOver.card_coker_dvr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:41.041859+00:00
-- url     : https://prove2.me/theorems/9d3b3e17-a958-5177-914a-eb01416a9818
-- title:
--   Frame Over: card coker dvr
-- statement:
--   The Frame Over construction uses the card coker dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L17-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeCountBoundFrames.lean#L17-L68

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameOver

theorem GlobalTheory.FrameOver.card_coker_dvr {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] {ϖ : R}
    (hϖ : Irreducible ϖ) (φ : M →ₗ[R] M) (n : ℕ) (hd : Associated (LinearMap.det φ) (ϖ ^ n)) :
    Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n := by sorry
