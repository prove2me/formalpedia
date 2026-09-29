-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period
-- name    : ModularCurve.JHNeronObjectAtP.exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/336c636f-3e4c-588a-acd5-37dc9a5d17ed
-- title:
--   Inertia displacements in TₚJ_H(M) lift to identity-reducing points
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial. Let $\mathrm{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $\mathrm{Pl}$ and algebraically closed residue field of characteristic $p$, let $hj$ witness that the $q$-expansion $j$ lies in the level-$1$ $q$-expansion function field, let $\mathfrak{X}$ be an `XHDRModelAtP` for $(p,M,H)$, and let $O$ be a `JHNeronObjectAtP` over the level data $\Lambda$; `hrep` asserts that the relative $\mathrm{Pic}^0$ designation formed from $O.G$, $O.g$ and the identity section of $O.L$ represents the functor of line bundles on the model `toBase p (ΓM M H) hj`, rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ and fibrewise algebraically equivalent to zero. Let $R_h$ be a henselian local domain mapping to $\overline{\mathbb{Q}}$, with every image in $\mathrm{Pl}$ and maximal ideal cut out by valuation $<1$. Let $\mathcal{G}$ be a $p$-divisible group of height $h$ over $R_h$, $\Delta$ an additive map $\mathcal{G}(\overline{\mathbb{Q}}) \to J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{F}_H)$, and $e$ a $\mathbb{Z}_p$-linear map of Tate modules (sequences $x_n$ with $p^n x_n = 0$, $p x_{n+1} = x_n$) computing $\Delta$ componentwise, whose range consists exactly of the sequences with $n$-th term in $O.\mathrm{finPts}(p^n)$. Assume `hinertF`: for $m > 0$, $\sigma$ in the inertia subgroup of $\mathrm{Pl}$ over $\mathbb{Q}$ and $m$-torsion $x$, $\sigma \cdot x - x \in O.\mathrm{finPts}(m)$. Assume further a $p$-divisible group $\mathcal{B}$ over $R_h$ with bialgebra maps $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$ such that `hrefl`: a point of $\mathcal{G}$ at level $v$ reduces to the counit (all values have valuation $<1$ away from the counit) as soon as its composite with $\psi_v$ does; and `hper`: whenever $\Delta$ of the class of a level-$v$ point $y$ equals $\sigma \cdot z - z$ for inertia $\sigma$ and $p^v$-torsion $z$, the composite of $y$ with $\psi_v$ reduces to the counit. Conclusion: for every $\tau$ in the inertia subgroup of $\mathrm{Pl}$ over $\mathbb{Q}$ and every $x \in T_p J_H(M)$ there is $y$ in the Tate module of $\mathcal{G}(\overline{\mathbb{Q}})$ with $e\,y = \tau x - x$ and such that for each $n$ some level $w$ and point $f$ of $\mathcal{G}$ at level $w$ has class equal to $y_n$ and reduces to the counit.
--
--   This is the Tate-module packaging of the finite-part and period statements at a place above $p$ for the Jacobian of $X_H(M)$ with $p \parallel M$: inertia displacements of arbitrary classes lie in the part coming from $\mathcal{G}$, and at each level they are represented by points reducing to the identity, that is lying in the connected (formal) part. It feeds the computation of the inertia action on the corner submodule of $T_pJ_H(M)$ in the ordinary case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.JHNeronObjectAtP.exists_eq_tateGaloisRep_sub_self_and_reduction_of_mem_inertiaSubgroupIn_of_reflects_of_period
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (hrange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))

    (hinertF : ∀ (m : ℕ), 0 < m → ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ x ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) m,
        σ • x - x ∈ O.finPts m)

    {hB : ℕ} (ℬ : PDivisibleGroup Rh p hB) (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    (hrefl : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
              algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
              algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hper : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
              algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) :
    ∀ τ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x : TateModule p (ModularCurve.JH M H),
      ∃ y : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e y = ModularCurve.JH.tateGaloisRep M H p τ x - x ∧
        ∀ n : ℕ, ∃ (w : ℕ) (f : 𝒢.Point (AlgebraicClosure ℚ) w),
          𝒢.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul f) =
            (y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n ∧
          ∀ a : 𝒢.level w, Pl.valuation (PDivisibleGroup.Point.toAlgHom f a -
            algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1 := by sorry
