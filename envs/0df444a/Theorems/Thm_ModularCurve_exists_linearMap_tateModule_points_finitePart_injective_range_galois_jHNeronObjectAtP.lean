-- Prove2me | Theorems.Thm_ModularCurve_exists_linearMap_tateModule_points_finitePart_injective_range_galois_jHNeronObjectAtP
-- name    : ModularCurve.exists_linearMap_tateModule_points_finitePart_injective_range_galois_jHNeronObjectAtP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/2542784a-d2fd-561c-8e2e-245c547cf52e
-- title:
--   Tate module comparison for the finite part of J_H
-- statement:
--   Fix natural numbers $p$ (prime) and $M\neq 0$, a subgroup $H\le(\mathbb{Z}/M)^\times$, and assume $p\mid M$, $p^2\nmid M$, that every unit of $(\mathbb{Z}/M)^\times$ mapping to $1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$, and $M/p\neq 0$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}=\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $p$ a non-unit of $Pl$ and with algebraically closed residue field of characteristic $p$, and let $hj$ record that the $q$-expansion `jqModC` of $j$ lies in the full-level $q$-expansion function field over $\mathbb{Q}$. Let $\mathfrak{X}$ be an `XHDRModelAtP` datum for $p,M,H$, let $\Lambda$ be a `LevelData` and $O$ a `JHNeronObjectAtP` over $Pl$ relative to $\Lambda$, so in particular $O$ gives a smooth separated group scheme $O.G\to\operatorname{Spec} R_p$ with $J_H(M)\simeq$ its sections over the generic point. Assume further the two representability data `hrep`, `hrepΛ`: the designations built from $(O.G,O.g)$ and from $(\Lambda.X,\Lambda.f)$, with their unit sections, represent the subfunctor of the relative Picard functor of the two-chart integral models at levels $\Gamma_M$ and $\Gamma_N$, rigidified along $\mathfrak{X}.\varepsilon_\infty$ (respectively along $\mathfrak{X}.\varepsilon_\infty$ followed by $\mathfrak{X}.\pi$), cut out by the condition that the rigidified line bundle be fibrewise algebraically equivalent to zero. Let $Rh$ be a Henselian local domain, an algebra over $\overline{\mathbb{Q}}$ with injective structure map, whose image lies in $Pl$ and for which $x$ lies in the maximal ideal exactly when its image has valuation $<1$. Let $\mathcal{G}$ be a $p$-divisible group of height $h$ over $Rh$ and $\Delta:\mathcal{G}(\overline{\mathbb{Q}})\to J_H(M)$ an injective additive map such that, for every $v$, an element $y\in J_H(M)$ lies in $O.\mathrm{finPts}(p^v)$ precisely when $y=\Delta(z)$ for some point of $\mathcal{G}$ of level $v$ over $\overline{\mathbb{Q}}$, and such that $\Delta(\tau'\cdot z)=\tau\cdot\Delta(z)$ whenever $\tau\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and an $Rh$-algebra automorphism $\tau'$ of $\overline{\mathbb{Q}}$ agree pointwise. The conclusion asserts the existence of a $\mathbb{Z}_p$-linear map $e$ from the Tate module of $\mathcal{G}(\overline{\mathbb{Q}})$ to that of $J_H(M)$ — Tate modules being the groups of sequences $(x_n)$ with $p^nx_n=0$ and $px_{n+1}=x_n$ — such that $(e\,x)_n=\Delta(x_n)$ for all $n$, $e$ is injective, a sequence $y$ lies in the range of $e$ if and only if $y_n\in O.\mathrm{finPts}(p^n)$ for every $n$, and $e$ intertwines the action of $\tau'$ on the Tate module of $\mathcal{G}(\overline{\mathbb{Q}})$ with the action of $\tau$ through [`ModularCurve.JH.tateGaloisRep`](def/ModularCurve_XH.html#L154) whenever $\tau'$ and $\tau$ agree pointwise.
--
--   This packages the levelwise identification of the points of a $p$-divisible group over the Henselian base with the $p$-power torsion of $J_H(M)$ extending to the place determined by $Pl$ into a single $\mathbb{Z}_p$-linear, Galois-equivariant injection of Tate modules whose image is exactly the finite part. It is used in the proof of the existence statement producing such a $p$-divisible group together with the closed immersion into the Raynaud extension for the Néron object at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearMap_tateModule_points_finitePart_injective_range_galois_jHNeronObjectAtP.lean

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

theorem ModularCurve.exists_linearMap_tateModule_points_finitePart_injective_range_galois_jHNeronObjectAtP
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    :
    ∃ e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H),
      (∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n)) ∧
      Function.Injective e ∧
      (∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n)) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x)) := by sorry
