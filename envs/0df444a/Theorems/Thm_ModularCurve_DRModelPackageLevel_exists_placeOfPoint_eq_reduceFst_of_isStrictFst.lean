-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceFst_of_isStrictFst
-- name    : ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceFst_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/cf86ff65-8f08-538c-85f9-bde80fefd892
-- title:
--   Strict places of the first kind reduce into the first component
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, and let $\mathfrak P$ be a package `DRModelPackageLevel N₀ p hpN₀` for the Igusa scheme $X(N_0p)$ over $R_p$, carrying among other data a curve model `𝔓.Meta` of the level-$N_0p$ function field over $\overline{\mathbf Q}$ with its isomorphism `𝔓.eeta` onto the generic fibre, a self-map `𝔓.w` over the base, a morphism `𝔓.π` to $X_0(N_0)$, and, for each $R_p$-algebra structure on a field, a curve model `𝔓.Mfib` with a morphism `𝔓.efib` to the corresponding fibre of $X_0(N_0)$ and two morphisms `𝔓.comp … 0`, `𝔓.comp … 1` from that fibre to the fibre of $X(N_0p)$. Let $A\subseteq\overline{\mathbf Q}$ be a valuation subring in which $p$ is a non-unit, $\rho\colon R_p\to A$ a ring homomorphism whose composition with the inclusion $A\hookrightarrow\overline{\mathbf Q}$ is the structure map, $\kappa$ an algebraically closed field of characteristic $p$ and $\mathrm{red}\colon A\to\kappa$ a ring homomorphism, so that $\kappa$ is an $R_p$-algebra via $\mathrm{red}\circ\rho$. Let `data` be modular polynomial data for $p$ (a monic $\Phi$ of degree $\psi(p)$ annihilating the pair $(j,j_p)$), `hKr` the Kronecker congruence $\Phi\equiv (X^p-Y)(X-Y^p)$ mod $p$, and $h_\alpha,h_\beta$ the integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N_0$ into the level-$N_0p$ function field over $\overline{\mathbf Q}$. Let $P$ be a `PlaceSpecialization` for these data: a map $\mathrm{sp}$ from places of the level-$N_0$ function field over $\overline{\mathbf Q}$ to places of `modularFunctionFieldC κ N₀`, a homomorphism on degree-zero divisor classes, and compatibilities with $\mathrm{red}$ on orders of $j$-functions; write $P.\mathrm{reduceFst}(W)=\mathrm{sp}(W|_{\alpha})$ and $P.\mathrm{reduceSnd}(W)=\mathrm{sp}(W|_{\beta})$ for the restrictions along the two embeddings. Two hypotheses are assumed, for every $\overline{\mathbf Q}$-point $y$ of `𝔓.Meta.C` over the base, every $A$-point $u$ of $X(N_0p)$ over $\mathrm{Spec}(\rho)$ restricting at the generic point to $y$, and every $\kappa$-point $u_\kappa$ of the fibre whose first projection is $\mathrm{Spec}(\mathrm{red})$ followed by $u$ and whose second projection is the identity, provided the place $\mathfrak P.\mathrm{Meta}.\mathrm{pointEquivPlace}(y)$ is strict of the first or of the second kind: any closed point of `𝔓.Mfib` whose image under `𝔓.efib` is the image of the closed point of $\kappa$ under $u_\kappa$ followed by `fibreMap0 𝔓.π` has place $P.\mathrm{reduceFst}$ of that place, and likewise with $u_\kappa$ followed by the fibre map of `𝔓.w.hom` and then `fibreMap0 𝔓.π` and with $P.\mathrm{reduceSnd}$. Now let $x_W$ be a $\overline{\mathbf Q}$-point of `𝔓.Meta.C` over the base whose place $W$ is strict of the first kind, that is $\mathrm{Frob}(P.\mathrm{reduceFst}\,W)=P.\mathrm{reduceSnd}\,W$ and $\mathrm{Frob}^2(P.\mathrm{reduceFst}\,W)\neq P.\mathrm{reduceFst}\,W$ for `frobOnPlacesGeomLevel κ N₀ data hKr`; let $t$ be an $A$-point of $X(N_0p)$ over $\mathrm{Spec}(\rho)$ whose restriction along $A\hookrightarrow\overline{\mathbf Q}$ is the point of the generic fibre determined by $x_W$, and $t_\kappa$ a $\kappa$-point of the fibre with first projection $\mathrm{Spec}(\mathrm{red})$ followed by $t$ and second projection the identity. Then there is a closed point $P_0$ of `𝔓.Mfib κ (algebraMap (R p) κ)` whose image under `𝔓.efib` followed by `𝔓.comp κ (algebraMap (R p) κ) 0` is the image of the closed point of $\kappa$ under $t_\kappa$ and whose place is $P.\mathrm{reduceFst}(W)$, and that image point of $t_\kappa$ does not lie in the range of the base map of `𝔓.comp κ (algebraMap (R p) κ) 1`.
--
--   In the Deligne–Rapoport description the special fibre at $p$ of $X_0(N_0p)$ is two copies of $X_0(N_0)_\kappa$ crossing at the supersingular points, the forgetful map being the identity on one and Frobenius on the other; this statement locates the reduction of an $A$-point whose generic place is strict of the first kind on the first copy only, at the closed point whose place is the one predicted by the place specialisation. It feeds the glueing arguments that compare the two reductions of a place and the computations of Atkin–Lehner and component behaviour used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceFst_of_isStrictFst.lean

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

theorem ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceFst_of_isStrictFst
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
      (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace xW))

      (t : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : barPt A ≫ t.1 = xW.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
      (tκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
      (_ : tκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ t.1) (_ : tκ ≫ pullback.snd _ _ = 𝟙 _),
      (∃ (P0 : closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C),
          (𝔓.efib κ (algebraMap (R p) κ) ≫ 𝔓.comp κ (algebraMap (R p) κ) 0).base P0.1 =
            tκ.base (IsLocalRing.closedPoint κ) ∧
          (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace xW)) ∧
      tκ.base (IsLocalRing.closedPoint κ) ∉ Set.range (𝔓.comp κ (algebraMap (R p) κ) 1).base := by sorry
