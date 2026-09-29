-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd
-- name    : ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/65389aac-fc7f-5d51-a5ef-e786a5bfe649
-- title:
--   Strict second-kind places reduce onto the second DR component
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ p hpN₀`: a Deligne–Rapoport model of the Igusa scheme `X N₀ p` over $R_p$, carrying a curve model `𝔓.Meta` over $\overline{\mathbb Q}$ with function field `modularFunctionFieldBar (N₀ * p)`, an isomorphism `𝔓.eeta` of it with the base change of `toBase N₀ p` to $\overline{\mathbb Q}$, a degeneracy map `𝔓.π` over the base to `X0 N₀ p`, and a self-map `𝔓.w.hom` over the base. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, let $\rho : R_p \to A$ satisfy that its composite with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is the structure map, let $\kappa$ be an algebraically closed field of characteristic $p$ and $\mathrm{red} : A \to \kappa$ a ring homomorphism, $\kappa$ being an $R_p$-algebra through $\mathrm{red}\circ\rho$. Let `data` be a modular polynomial datum for $p$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(p)$ annihilating the pair of $q$-expansions) satisfying the Kronecker congruence, let $h_\alpha, h_\beta$ assert that the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` of level $N_0$ into level $N_0p$ over $\overline{\mathbb Q}$ are integral, and let $P$ be a `PlaceSpecialization`, whose map $P.\mathrm{sp}$ sends places of `modularFunctionFieldBar N₀` to places of `modularFunctionFieldC κ N₀`; write $P.\mathrm{reduceFst}\,W = P.\mathrm{sp}$ of the restriction of $W$ along `heckeAlphaBar`, and $P.\mathrm{reduceSnd}\,W$ likewise along `heckeBetaBar`. Two compatibility hypotheses are assumed, each quantified over: a $\overline{\mathbb Q}$-point $y$ of `𝔓.Meta.C` over the base, an $A$-point $u$ of `X N₀ p` over $\operatorname{Spec}\rho$ whose restriction along `barPt A` agrees with $y$ transported by `𝔓.eeta` to the generic fibre, a $\kappa$-point $u_\kappa$ of `fibre (algebraMap (R p) κ)` which is a section of the second projection and whose first projection is $u$ composed with $\operatorname{Spec}(\mathrm{red})$, and the assumption that the place `𝔓.Meta.pointEquivPlace y` is strict of the first or of the second kind for $P$; the first hypothesis says that any closed point $P_0$ of `(𝔓.Mfib κ _).C` whose image under `𝔓.efib κ _` equals the image of the closed point of $\kappa$ under $u_\kappa$ followed by `fibreMap0 𝔓.π` has place $P.\mathrm{reduceFst}$ of that place, and the second the same with `fibreMap 𝔓.w.hom 𝔓.w_over` inserted before `fibreMap0 𝔓.π` and $P.\mathrm{reduceSnd}$ in place of $P.\mathrm{reduceFst}$. Here strictness of the second kind for a place $W$ means $P.\mathrm{reduceFst}\,W = \mathrm{frobOnPlacesGeomLevel}(P.\mathrm{reduceSnd}\,W)$ while the second Frobenius iterate of $P.\mathrm{reduceSnd}\,W$ differs from $P.\mathrm{reduceSnd}\,W$. Now let $x_W$ be a $\overline{\mathbb Q}$-point of `𝔓.Meta.C` over the base whose place is strict of the second kind, $t$ an $A$-point of `X N₀ p` over $\operatorname{Spec}\rho$ restricting to $x_W$ on the generic fibre, and $t_\kappa$ a $\kappa$-point of the fibre which is a section of the second projection and reduces $t$. The conclusion is twofold: there is a closed point $P_1$ of `(𝔓.Mfib κ _).C` whose image under `𝔓.efib κ _` followed by `𝔓.comp κ _ 1` is the image of the closed point of $\kappa$ under $t_\kappa$ and whose place is $P.\mathrm{reduceSnd}$ of the place of $x_W$; and the image of the closed point of $\kappa$ under $t_\kappa$ does not lie in the range of the underlying map of `𝔓.comp κ _ 0`.
--
--   This records, for the Deligne–Rapoport model of $X_0(N_0p)$ at $p$, that the reduction of a point whose place is strict of the second kind lands on the second of the two components of the special fibre and off the first, at exactly the point of the level-$N_0$ model over $\kappa$ predicted by $P.\mathrm{reduceSnd}$. It is used, together with its first-kind counterpart, by the glueing statements that compare places on the two components and feed the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (red : ↥A →+* κ) :
    letI : Algebra (R p) κ := (red.comp ρ).toAlgebra
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr κ red hα hβ)

      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C),
          (𝔓.efib κ (algebraMap (R p) κ)).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base (IsLocalRing.closedPoint κ) →
            (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C),
          (𝔓.efib κ (algebraMap (R p) κ)).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base
                (IsLocalRing.closedPoint κ) →
            (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y))
      (xW : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (_ : P.IsStrictSnd (𝔓.Meta.pointEquivPlace xW))
      (t : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : barPt A ≫ t.1 = xW.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
      (tκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
      (_ : tκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ t.1) (_ : tκ ≫ pullback.snd _ _ = 𝟙 _),
      (∃ (P1 : closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C),
          (𝔓.efib κ (algebraMap (R p) κ) ≫ 𝔓.comp κ (algebraMap (R p) κ) 1).base P1.1 =
            tκ.base (IsLocalRing.closedPoint κ) ∧
          (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace xW)) ∧
      tκ.base (IsLocalRing.closedPoint κ) ∉ Set.range (𝔓.comp κ (algebraMap (R p) κ) 0).base := by sorry
