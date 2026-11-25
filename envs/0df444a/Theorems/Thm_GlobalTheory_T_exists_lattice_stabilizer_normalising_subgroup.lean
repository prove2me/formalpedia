-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_lattice_stabilizer_normalising_subgroup
-- name    : GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:45:15.210529+00:00
-- url     : https://prove2.me/theorems/b9ed818a-5f2d-4fd6-a6ce-155d69bfa735
-- title:
--   T: exists lattice stabilizer normalising subgroup
-- statement:
--   The T construction uses the exists lattice stabilizer normalising subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroupStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroupStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroupStatement
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

theorem GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', ∃ Λ : Submodule L.O S.V, IsLat L Λ ∧ S.St ⊓ stabL L Λ = S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ⊓ stabL L (Submodule.span L.O (Set.range fun b => n' (S.f' b))) ∧ S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) ≤ S.St ⊓ stabL L Λ ∧ ∀ h ∈ S.St ⊓ stabL L Λ, CongId L S.ϖ Λ 1 h → h ∈ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) := by sorry
