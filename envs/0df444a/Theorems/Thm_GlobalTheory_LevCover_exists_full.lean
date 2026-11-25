-- Prove2me | Theorems.Thm_GlobalTheory_LevCover_exists_full
-- name    : GlobalTheory.LevCover.exists_full
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:25.850575+00:00
-- url     : https://prove2.me/theorems/67779d17-30f5-4a1b-bfa4-0e3df57cdee4
-- title:
--   Lev Cover: exists full
-- statement:
--   The Lev Cover construction uses the exists full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SpMapComp.lean#L61-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SpMapComp.lean#L61-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}

theorem GlobalTheory.LevCover.exists_full (t : SAB H S) {B L : Type} [Field B] [CharZero B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (s : S ⟶ Sp B) {N : ℕ} (hN : 0 < N) {ξ : Lˣ} (hξ : ξ ^ N = 1)
    {Z : Over S} {et : D.La → (Z ⟶ t.G)} (R : RepTors t.G N D.La Z et)
    (hW : ∀ (T : Over S) (x y : T ⟶ t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
      c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs t.G t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (W : Over S) (α : D.La → (W ⟶ t.G)), IsFinite W.hom ∧ Etale W.hom ∧ (∀ a c, α (a + c) = α a * α c) ∧
      (∀ a, α a ^ N = 1) ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
        ∀ α' : D.La → (Over.mk x ⟶ t.G), (∀ a c, α' (a + c) = α' a * α' c) → (∀ a, α' a ^ N = 1) →
          ((∃ w : Over.mk x ⟶ W, ∀ a, w ≫ α a = α' a) ↔ ∃ β' : L →+* k, β'.comp (algebraMap B L) = β ∧
            (∀ (c : 𝓞 E) a, α' (c • a) = α' a ≫ t.act.act c) ∧
            ∀ a b, Out.WeilIs t.G t.PP.L N (α' a) (α' b) (unitOn (Units.map β'.toMonoidHom ξ ^ D.EF a b))) := by sorry
