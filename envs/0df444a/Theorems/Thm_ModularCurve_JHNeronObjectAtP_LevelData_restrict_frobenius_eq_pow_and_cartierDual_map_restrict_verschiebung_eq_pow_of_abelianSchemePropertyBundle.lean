-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/54950892-5f93-59b0-8048-830701256ddd
-- title:
--   Frobenius and Verschiebung on the p-divisible levels mod p
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, and level data $\Lambda$ for $(p,M,H,A)$, consisting of a structure morphism $\sigma_A$ with $\bar{\cdot}$-compatibility, a scheme $\Lambda.X$ with morphism $\Lambda.f$ to $\operatorname{Spec}$ of `baseRing p` (the rationals with denominator coprime to $p$), a relative group law $\Lambda.L$ on $\Lambda.f$, and identifications of generic and special points. Assume `AbelianSchemePropertyBundle` for $\Lambda.f$: $\Lambda.f$ is smooth and proper, every fibre is connected, and a relative group law exists. Let $\sigma_p$ be $\operatorname{Spec}$ of the algebra map `baseRing p` $\to \mathbb{Z}/p$, and $\mathcal{A}$ a $p$-divisible group over `baseRing p` of height $h$ (finite free cocommutative Hopf levels with surjective transitions, $\operatorname{rank} = p^{vh}$, kernels of transitions the $p^v$-torsion ideals). For each $v$ let $\iota'_v : \operatorname{Spec}((\mathcal{A} \otimes \mathbb{Z}/p).\mathrm{level}\,v) \to \Lambda.X \times_{\operatorname{base}} \operatorname{Spec}(\mathbb{Z}/p)$ be a closed immersion over $\mathbb{Z}/p$, compatible with the transition maps, a homomorphism on points valued in any $\mathbb{Z}/p$-algebra, and inducing an isomorphism onto the fibre product of the multiplication-by-$p^v$ map of the base-changed group law with its unit section. Let $F, V$ be endomorphisms of the special fibre over $\mathbb{Z}/p$ such that composing any point over a characteristic-$p$ $\mathbb{Z}/p$-algebra $B$ with $F$ is precomposition with $\operatorname{Spec}$ of the $p$-th power map on $B$, with $V \,\text{then}\, F = F \,\text{then}\, V = [p]$ and $V$ a homomorphism for the group law. Finally let $\varphi_F(v), \varphi_V(v)$ be bialgebra endomorphisms of the $v$-th level over $\mathbb{Z}/p$ whose $\operatorname{Spec}$ intertwines $\iota'_v$ with $F$, respectively $V$. Then $\varphi_F(v)(a) = a^p$ for all $v$ and all $a$ in the $v$-th level, and $\operatorname{CartierDual.map}(\varphi_V(v))(\chi) = \chi^p$ for every $\chi$ in the Cartier dual (the $\mathbb{Z}/p$-linear dual) of the $v$-th level.
--
--   This identifies, on the $p^v$-torsion levels of the $p$-divisible group attached to the reduction mod $p$ of the Jacobian-type scheme $\Lambda.X$, the relative Frobenius with the $p$-th power map on the level Hopf algebra and the Verschiebung with the endomorphism whose Cartier transpose is $\chi \mapsto \chi^p$. It feeds the two-step tower and Raynaud-quotient descent step used in [`ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins`](thm.html#ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.JZeroNeronObjectAtP

open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.LevelData.restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)

    {h : ℕ} (𝒜 : PDivisibleGroup (baseRing p) p h)
    [Algebra (baseRing p) (ZMod p)]
    (hσp : σp = Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (ZMod p))))
    (ι' : ∀ v : ℕ, Spec (CommRingCat.of ((𝒜.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
    (hι'base : ∀ v : ℕ, ι' v ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))
    (hι'cl : ∀ v : ℕ, IsClosedImmersion (ι' v))
    (hι'p : ∀ (v : ℕ), ∃ h3 : ι' v ≫ (Λ.L.baseChange σp).schemeNsmul (p ^ v) =
          (ι' v ≫ pullback.snd Λ.f σp) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1,
      IsIso (pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v)) (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1)
        (ι' v) (ι' v ≫ pullback.snd Λ.f σp) h3))

    (hι'mul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒜.baseChange (ZMod p)).Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v =
          ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (hι't : ∀ v : ℕ, Spec.map (CommRingCat.ofHom
          ((𝒜.baseChange (ZMod p)).transition v : (𝒜.baseChange (ZMod p)).level (v + 1) →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' (v + 1) = ι' v)

    (F V : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x F).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)
    (hVF : V.1 ≫ F.1 = (Λ.L.baseChange σp).schemeNsmul p)
    (hFV : F.1 ≫ V.1 = (Λ.L.baseChange σp).schemeNsmul p)
    (hVmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) V =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x V) (schemeHomOverComp y V))

    (φF φV : ∀ v : ℕ, (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v)
    (hφF : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φF v : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' v = ι' v ≫ F.1)
    (hφV : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φV v : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' v = ι' v ≫ V.1) :
    (∀ (v : ℕ) (a : (𝒜.baseChange (ZMod p)).level v), φF v a = a ^ p) ∧
    (∀ (v : ℕ) (χ : CartierDual (ZMod p) ((𝒜.baseChange (ZMod p)).level v)), CartierDual.map (φV v) χ = χ ^ p) := by sorry
