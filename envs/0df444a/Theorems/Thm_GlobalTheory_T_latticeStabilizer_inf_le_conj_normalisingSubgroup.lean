-- Prove2me | Theorems.Thm_GlobalTheory_T_latticeStabilizer_inf_le_conj_normalisingSubgroup
-- name    : GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:57:13.472931+00:00
-- url     : https://prove2.me/theorems/60eff020-d8ee-5271-bb19-b012cd70dfb7
-- title:
--   T: lattice Stabilizer inf le conj normalising Subgroup
-- statement:
--   The T construction uses the lattice Stabilizer inf le conj normalising Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeStabilizerInfLeConjNormalisingSubgroupStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatticeStabilizerInfLeConjNormalisingSubgroupStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroup
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroupStatement
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

theorem GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∃ h ∈ S.St, S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ≤ MulAut.conj h • S.K0 ∧ ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ ∀ j, h⁻¹ (n (S.f j)) = ∑ i, u i j • S.f i := by sorry
