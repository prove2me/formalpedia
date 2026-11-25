-- Prove2me | Theorems.Thm_GlobalTheory_DiscOver_disc_fin
-- name    : GlobalTheory.DiscOver.disc_fin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:25:34.913413+00:00
-- url     : https://prove2.me/theorems/557c3957-eacc-49ec-b5da-c29291147e49
-- title:
--   Disc Over: disc fin
-- statement:
--   The Disc Over construction uses the disc fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L141-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L141-L245

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpan
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
open GlobalTheory GlobalTheory.DiscOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.DiscOver.disc_fin [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m : ℕ}
    (v : Fin m → Fin n → E) (c : F) (hc : c ≠ 0) (hG : (gram L Hm v).det = algebraMap F E c)
    (Mh Md : Submodule L.O (Fin n → E)) (h1 : Submodule.span L.O (Set.range v) ≤ Mh)
    (h2 : ∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v))
    (h3 : ∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O)
    (h4 : ∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) :
    0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup *
      ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 =
      resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧
      (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧
      ∃ b : Fin m → Fin n → E, Md = Submodule.span L.O (Set.range b) := by sorry
