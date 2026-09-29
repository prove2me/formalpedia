-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing
-- name    : ModularCurve.DRModelPackageLevel.reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/5e47c6ed-48f2-5074-924a-0303078cb011
-- title:
--   Points through a crossing have supersingular first reduction
-- statement:
--   Fix natural numbers $N_0$ and a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport model package $\mathfrak{P}$ of level $N_0p$ over $R p$ (the localisation of $\mathbb{Z}$ at $p$), a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, a ring map $\rho : R p \to A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map, an algebraically closed field $\kappa$ of characteristic $p$, and a ring map $\mathrm{red} : A \to \kappa$, making $\kappa$ an $R p$-algebra via $\mathrm{red}\circ\rho$. Assume given: modular polynomial data `data` for $p$ satisfying the Kronecker congruence, integrality of the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` at level $(N_0,p)$, a specialisation package $P$ of type `PlaceSpecialization A p N₀ data hKr κ red hα hβ`, the hypothesis that $\mathrm{red}\,c=0$ exactly for $c$ in the maximal ideal of $A$, a $\overline{\mathbb{Q}}$-section $y$ of $\mathfrak{P}.\mathrm{Meta}.\mathrm{toBase}$, a morphism $u : \operatorname{Spec} A \to X N_0 p$ over $\operatorname{Spec}\rho$ whose restriction along $A \hookrightarrow \overline{\mathbb{Q}}$ is $y$ transported through $\mathfrak{P}.\mathrm{eeta}$ and the first projection, a $\kappa$-section $u_\kappa$ of the fibre of `toBase` over $\kappa$ reducing $u$ along $\mathrm{red}$, and a point $n$ of the pullback of the two component maps $\mathfrak{P}.\mathrm{comp}\,\kappa\,0$, $\mathfrak{P}.\mathrm{comp}\,\kappa\,1$ whose image in the special fibre is the closed point of $u_\kappa$. The conclusion is that $P.\mathrm{reduceFst}$ of the place attached to $y$ by $\mathfrak{P}.\mathrm{Meta}.\mathrm{pointEquivPlace}$, that is $P.\mathrm{sp}$ applied to the restriction of that place along `heckeAlphaBar`, lies in $\mathrm{ssPlaces}\,p\,N_0\,\kappa$: it is rational, affine geometric, and its value at $\mathrm{jGeomGen}$ lies in $\mathrm{ssJSet}\,p\,\kappa$.
--
--   This is the geometric input that crossings of the two components of the Deligne–Rapoport special fibre of $X_0(N_0p)$ in characteristic $p$ are the supersingular points: an $A$-valued point of the model whose closed point is a crossing has first reduction a supersingular place of the characteristic-$p$ modular function field. It feeds the exclusion of simultaneous strictness and supersingular first reduction used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_CharPReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (red : ↥A →+* κ) :
    letI : Algebra (R p) κ := (red.comp ρ).toAlgebra
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr κ red hα hβ)
      (_ : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
      (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (n : ↥(pullback (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1)))
      (_ : (pullback.fst (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1) ≫ 𝔓.comp κ (algebraMap (R p) κ) 0).base n =
        uκ.base (IsLocalRing.closedPoint κ)),
      P.reduceFst (𝔓.Meta.pointEquivPlace y) ∈ ssPlaces p N₀ κ := by sorry
