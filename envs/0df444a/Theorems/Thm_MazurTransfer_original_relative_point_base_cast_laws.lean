-- Prove2me | Theorems.Thm_MazurTransfer_original_relative_point_base_cast_laws
-- name    : MazurTransfer.original_relative_point_base_cast_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T02:48:26.277997+00:00
-- url     : https://prove2.me/theorems/0082452c-4d88-4836-a792-d335602dba16
-- statement:
--   Changing only a proved-equal base arrow gives the original relative point equivalence with the same underlying scheme map. It commutes with the original endomorphism and every original test-scheme precomposition, and preserves the original relative group identity and multiplication. All original schemes, maps, equality and commutative-ring hypotheses and universes are retained. Named downstream consumer: coefficient-map comparison between the same integral nineteen Hopf points and fixed arithmetic norm-kernel points.

import Definitions.Def_MazurTransfer_OriginalRelativePointBaseCastData20261020
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativePointBaseCast
universe u

theorem MazurTransfer.original_relative_point_base_cast_laws : (∀ {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}, ∀ (h : t = t') (x : SchemeHomOver t f),
(pointEquiv h x).val = x.val) ∧ (∀ {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}, ∀ (h : t = t') (F : SchemeHomOver f f)
    (x : SchemeHomOver t f),
pointEquiv h (NeronModelInfra.schemeHomOverComp x F) =
      NeronModelInfra.schemeHomOverComp (pointEquiv h x) F) ∧ (∀ {B A T : Scheme.{u}} {f : A ⟶ B} {t t' : T ⟶ B}, ∀ {T' : Scheme.{u}} {s s' : T' ⟶ B}
    (h : t = t') (hs : s = s') (ψ : T' ⟶ T) (hψ : ψ ≫ t = s) (hψ' : ψ ≫ t' = s')
    (x : SchemeHomOver t f),
pointEquiv hs (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ' (pointEquiv h x)) ∧ (∀ {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {t t' : T ⟶ Spec (CommRingCat.of R)}, ∀ (h : t = t'),
pointEquiv h (L.one t) = L.one t') ∧ (∀ {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {t t' : T ⟶ Spec (CommRingCat.of R)}, ∀ (h : t = t') (x y : SchemeHomOver t f),
pointEquiv h (L.mul t x y) = L.mul t' (pointEquiv h x) (pointEquiv h y)) := by sorry
