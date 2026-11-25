-- Prove2me | Theorems.Thm_GlobalTheory_HL_SelfDual_orthonormal_basis_and_one_orbit
-- name    : GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:08:13.709849+00:00
-- url     : https://prove2.me/theorems/c6bdfd31-a95e-44e9-b80b-c3757344fb3e
-- title:
--   Self Dual: orthonormal basis and one orbit
-- statement:
--   The Self Dual construction uses the orthonormal basis and one orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrthonormalBasisAndOneOrbit.lean#L268-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrthonormalBasisAndOneOrbit.lean#L268-L276

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → (∀ Λ, IsSD L Hm Λ → ∃ b : Fin n → Fin n → E, (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) ∧ Λ = Submodule.span L.O (Set.range b)) ∧ ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∃ g ∈ isomG L Hm, g • Λ = Λ' := by sorry
