-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_levelData_pts_add_and_ptsSp_add_of_surjective_degPts
-- name    : ModularCurve.JHNeronObjectAtP.levelData_pts_add_and_ptsSp_add_of_surjective_degPts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/9c3bcdb3-c81b-5876-8fca-929e72437d26
-- title:
--   Additivity of the level-M/p point dictionaries Λ
-- statement:
--   Fix a prime $p$, a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the predicate `LiesOverPrime`), whose residue field has characteristic $p$ and is algebraically closed. Let $\Lambda$ be level data in the sense of `JHNeronObjectAtP.LevelData`: a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb{Z}_{(p)}$ lifting the generic point, a scheme $X$ with structure morphism $f$ to the base, a relative group law $\Lambda.L$ on $f$, and bijections $\Lambda.\mathrm{pts}$ from $J_{H'}(M/p) = \mathrm{Pic}^0$ of the function field of $X_{H'}$ over $\overline{\mathbb{Q}}$ (with $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$) onto the points of $f$ over the generic point, and $\Lambda.\mathrm{ptsSp}$ from the degree-zero divisor class group $\mathrm{Pic}^0$ of the field `Fbar` over the residue field of $A$ onto the points of $f$ over $\operatorname{resPt} A \mathbin{\text{followed by}} \sigma_A$; let $O$ be a `JHNeronObjectAtP` over $\Lambda$. Assume: the map $O.\mathrm{degPts}\,0$ is surjective; there is a morphism $\mathrm{degPull0} \colon \Lambda.X \to O.G$ over the base, post-composition with which carries the $\Lambda.L$-product of any two points over any base morphism $s$ to the $O.L$-product of their images; and there is an endomorphism $F^*$ of $\mathrm{Pic}^0$ over the residue field such that, for every point $x$ of $f$ over $\operatorname{resPt} A$ followed by $\sigma_A$, the pair of divisor classes attached by `GluedPic0.toPic0Pair` (for the finite set $O.\mathrm{ssFinset}$) to $O.\mathrm{ptsSp}^{-1}$ of $x$ composed with $\mathrm{degPull0}$ equals $(\Lambda.\mathrm{ptsSp}^{-1}x,\ F^*(\Lambda.\mathrm{ptsSp}^{-1}x))$. The conclusion is twofold: $\Lambda.\mathrm{pts}$ is additive, $\Lambda.\mathrm{pts}(x+y) = \Lambda.L.\mathrm{mul}(\Lambda.\mathrm{pts}\,x, \Lambda.\mathrm{pts}\,y)$ over the generic point; and $\Lambda.\mathrm{ptsSp}$ is additive, $\Lambda.\mathrm{ptsSp}(x+y)$ being the point obtained by `ofFibrePt` from the product, in the base change of $\Lambda.L$ along $\operatorname{resPt} A$ followed by $\sigma_A$, of the fibre points of $\Lambda.\mathrm{ptsSp}\,x$ and $\Lambda.\mathrm{ptsSp}\,y$.
--
--   This supplies the two additivity properties of the level-$M/p$ point dictionaries, generic and special, that are the counterparts for $\Lambda$ of the fields $\mathrm{pts\_add}$ and $\mathrm{ptsSp\_add}$ built into the Néron object $O$ at level $M$. It is used in the $q$-new arguments on $J_H$, where degeneracy maps between the two levels and their Néron models are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_levelData_pts_add_and_ptsSp_add_of_surjective_degPts.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.levelData_pts_add_and_ptsSp_add_of_surjective_degPts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (hsurj : Function.Surjective (O.degPts 0))

    (degPull0 : SchemeHomOver Λ.f O.g)
    (hpull_mul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) degPull0 = O.L.mul s (schemeHomOverComp x degPull0) (schemeHomOverComp y degPull0))

    (Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hpullsp0 : ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f,
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x degPull0)) = (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))) :
    (∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y)) ∧
    (∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) := by sorry
