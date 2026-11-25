-- Prove2me | Theorems.Thm_GlobalTheory_T_congruence_subgroup_lattice_stabilizer
-- name    : GlobalTheory.T.congruence_subgroup_lattice_stabilizer
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:10:10.730448+00:00
-- url     : https://prove2.me/theorems/673770bb-c4ce-4e80-bff7-1a2f670a6fcd
-- title:
--   T: congruence subgroup lattice stabilizer
-- statement:
--   The T construction uses the congruence subgroup lattice stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizerStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizerStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizerStatement
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

theorem GlobalTheory.T.congruence_subgroup_lattice_stabilizer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Λ : Submodule L.O (Fin n → E)), IsLat L Λ → ∀ N : ℕ, (∃ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (∀ g, g ∈ K ↔ g ∈ stabL L Λ ∧ CongId L ϖ Λ N g) ∧ K.relIndex (stabL L Λ) ≠ 0 ∧ ∀ a ∈ stabL L Λ, MulAut.conj a • K = K) ∧ (1 ≤ N → ∀ g, CongId L ϖ Λ N g → g ∈ stabL L Λ) ∧ ∀ Λ', IsLat L Λ' → ∃ N' : ℕ, ∀ g, CongId L ϖ Λ N' g → CongId L ϖ Λ' N g := by sorry
