-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq_levelData
-- name    : ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq_levelData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/cb1e451e-0ccc-58b3-8724-c94db73d70cc
-- title:
--   Rigidity of homomorphic μ^t_m-points over a henselian place
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, whose residue field is of characteristic $p$ and algebraically closed. Let $\Lambda$ be a `LevelData` for $(p,M,H)$ over $A$: a structure morphism $\sigma_A : \operatorname{Spec} A \to \operatorname{Spec}(\mathbb{Z}_{(p)}\text{-type base ring } \mathtt{baseRing}\,p)$ restricting to the generic point along $\operatorname{Spec}\bar{\mathbb{Q}} \to \operatorname{Spec} A$, a scheme $\Lambda.X$ with morphism $\Lambda.f$ to the base, a relative group law $\Lambda.L$ on $\Lambda.f$, and identifications of the level-$(M/p)$ points and of $\mathrm{Pic}^0$ of the residual function field with sections of $\Lambda.f$ over the generic and the residual point. Assume $\Lambda.f$ is smooth and proper with connected fibres and admits a relative group law, that $\Lambda.L$ is commutative, and let $O$ be a `JHNeronObjectAtP` for $\Lambda$, with toric rank $t = O.\mathtt{toricRank}$. Let $m > 0$ be such that multiplication by $m$ for the group law obtained from $\Lambda.L$ by base change along $\sigma_A$ is locally quasi-finite, quasi-compact and flat. Let $u, v$ be two sections over $\mu^t_{m,A} = \operatorname{Spec}\big(A[(\mathbb{Z}/m)^t]\big)$ of the base change $\operatorname{pr}_2 : \Lambda.X \times_{\mathrm{base}} \operatorname{Spec} A \to \operatorname{Spec} A$, that is, $A$-morphisms from $\mu^t_{m,A}$ to the base-changed scheme. Assume that both are homomorphic on $\bar{\mathbb{Q}}$-points: for all $\chi, \chi'$ in the convolution monoid of $A$-algebra maps $A[(\mathbb{Z}/m)^t] \to \bar{\mathbb{Q}}$, precomposing $u$ (respectively $v$) with the point $\mu^t_{m}(\chi\chi')$ equals the product, under the base-changed group law, of the precompositions with $\mu^t_m(\chi)$ and $\mu^t_m(\chi')$. Assume finally that $u$ and $v$ agree after restriction along the reduction morphism $\mu^t_{m,\kappa} \to \mu^t_{m,A}$ induced by the residue map of $A$. Then $u = v$.
--
--   This is a rigidity statement in the style of SGA 3, Exp. IX, for homomorphisms of a split group of multiplicative type into the base change along $\sigma_A$ of the level-$(M/p)$ group scheme of the data $\Lambda$ over a place above $p$ with algebraically closed residue field: two such morphisms that are homomorphic on geometric points are determined by their special fibre. It is used in the analysis of the toric part of the reduction, being invoked in the proof that the degree of the points attached to the toric subset vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq_levelData.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq_levelData
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛcomm : ∀ {T : Scheme.{0}} (t : T ⟶ base p) (x y : SchemeHomOver t Λ.f), Λ.L.mul t x y = Λ.L.mul t y x)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (hΛm : LocallyQuasiFinite ((Λ.L.baseChange Λ.σA).schemeNsmul m) ∧
      QuasiCompact ((Λ.L.baseChange Λ.σA).schemeNsmul m) ∧ Flat ((Λ.L.baseChange Λ.σA).schemeNsmul m))
    (u v : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f))
    (hu : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) u =
        (Λ.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) u)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) u))
    (hv : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) v =
        (Λ.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) v)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) v))
    (huv : muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ u.1 =
      muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ v.1) :
    u = v := by sorry
