-- Prove2me | Theorems.Thm_GlobalTheory_HL_OverBasis_exists_basis_overlattice
-- name    : GlobalTheory.HL.OverBasis.exists_basis_overlattice
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:25.232514+00:00
-- url     : https://prove2.me/theorems/d67661d1-2201-562d-8ab4-e9056fd0a21b
-- title:
--   Over Basis: exists basis overlattice
-- statement:
--   The Over Basis construction uses the exists basis overlattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LinearIndependentOfGram.lean#L45-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LinearIndependentOfGram.lean#L45-L100

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LinearIndependentOfGram
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OverBasis
open Matrix GlobalTheory.HL.SelfDual
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.OverBasis.exists_basis_overlattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (y : Fin m → Fin n → E), IsUnit (gramT L Hm y).det → ∀ Mh : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range y) ≤ Mh → (∀ v ∈ Mh, v ∈ Submodule.span E (Set.range y)) → (∀ v ∈ Mh, ∀ w ∈ Mh, hf L Hm v w ∈ L.O) → LinearIndependent E y ∧ ∃ A : Matrix (Fin m) (Fin m) E, IsIntM L A ∧ IsUnit A.det ∧ Mh = Submodule.span L.O (Set.range (rmul y A⁻¹)) ∧ LinearIndependent E (rmul y A⁻¹) ∧ rmul (rmul y A⁻¹) A = y := by sorry
