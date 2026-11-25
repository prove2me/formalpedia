-- Prove2me | Theorems.Thm_GlobalTheory_T_relIndex_comap_pair_of_dense_image
-- name    : GlobalTheory.T.relIndex_comap_pair_of_dense_image
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:51.339075+00:00
-- url     : https://prove2.me/theorems/79e9bf1d-dddb-4627-a57f-71a1e6663e14
-- title:
--   T: rel Index comap pair of dense image
-- statement:
--   The T construction uses the rel Index comap pair of dense image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexComapPairOfDenseImageStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexComapPairOfDenseImageStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexComapPairOfDenseImage
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexComapPairOfDenseImageStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.relIndex_comap_pair_of_dense_image : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by sorry
