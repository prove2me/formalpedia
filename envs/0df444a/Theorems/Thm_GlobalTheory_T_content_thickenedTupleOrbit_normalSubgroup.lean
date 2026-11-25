-- Prove2me | Theorems.Thm_GlobalTheory_T_content_thickenedTupleOrbit_normalSubgroup
-- name    : GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:48:31.140145+00:00
-- url     : https://prove2.me/theorems/c215ea8a-f26a-4945-b821-c5db3be9642c
-- title:
--   T: content thickened Tuple Orbit normal Subgroup
-- statement:
--   The T construction uses the content thickened Tuple Orbit normal Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ContentThickenedTupleOrbitNormalSubgroupStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ContentThickenedTupleOrbitNormalSubgroupStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroup
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroupStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ K K' : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm → K' ≤ K → (∀ a ∈ K, MulAut.conj a • K' = K') → K'.relIndex K ≠ 0 → ∀ i : ℕ, 1 ≤ i → (∀ y ∈ torb K' x, ∀ A ∈ congK L ϖ m i, cT L A * gramT L Hm x * A = gramT L Hm x → rmul y A ∈ torb K' x) → IsCO (tupLat L Λs m) (thick L ϖ (torb K' x) i) → cont (tupLat L Λs m) (thick L ϖ (torb K x) i) * ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ K').relIndex (fixG L Hm (Submodule.span E (Set.range x)) ⊓ K) : ℝ) = (K'.relIndex K : ℝ) * cont (tupLat L Λs m) (thick L ϖ (torb K' x) i) := by sorry
