-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv
-- name    : ModularCurve.JZeroNeronIdentityComponent.exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/3ed625bd-9c71-5b1e-a3d5-a656092acfc5
-- title:
--   Eisenstein-primary Hopf orders and an H¹ comparison
-- statement:
--   Let $p,q$ be primes with $q$ dividing $|p-1|/\gcd(p-1,12)$, let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ a nonunit of $A$, and let $N$ be a Néron-identity-component datum for $J_0(p)$ over $\mathbf Z$: a smooth, separated, surjective group scheme $g\colon G\to\operatorname{Spec}\mathbf Z$ with commutative relative group law $N.L$, together with an additive, Galois- and Hecke-equivariant identification $N.\mathrm{pts}$ of $\mathrm{JZero}\,p=\mathrm{Pic}^0$ of the level-$p$ modular function field over $\overline{\mathbf Q}$ with the sections of $g$ over $\operatorname{Spec}\overline{\mathbf Q}$. Let $\mathcal G$ be an abelian sheaf on the small fppf site of $\operatorname{Spec}\mathbf Z$ together with bijections $e_U\colon\mathcal G(U)\to\{U\to G \text{ over } \mathbf Z\}$ carrying addition to $N.L$-multiplication and restriction to precomposition, and let $\rho\colon\mathbf T=\mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbf Z\to\operatorname{End}\mathcal G$ be a ring homomorphism such that each $t\in\mathbf T$ is induced, simultaneously on $\mathrm{JZero}\,p$ (for the module structure `heckeModuleBar p`) and on all sections of $\mathcal G$, by postcomposition with some endomorphism $\varphi$ of $G$ over $\mathbf Z$. Then there exists a torsion Hopf order $C$ for the family $V_m=\ker(q^m)\cap\bigcup_k(\mathfrak P^k\text{-torsion})$ in $\mathrm{JZero}\,p$, where $\mathfrak P=$ `eisensteinMaximalIdeal p q` is the preimage under `eisensteinEval p` of $(q)\subset\mathbf Z$ — that is, flat finite-type $\mathbf Z$-Hopf algebras $H_m$ with surjective level maps, generic points $V_m$, $A$-points the toric $q^m$-torsion in $V_m$, and finiteness away from $p$ — with the following property. For every $m$, every abelian fppf sheaf $\mathcal J$ on $\operatorname{Spec}\mathbf Z$ equipped with additive bijections $\mathcal J(U)\cong\mathrm{WithConv}(H_m\to_{\mathbf Z}\Gamma(U,\mathcal O))$ natural in $U$, and every $\mathbf T$-module structure on a universe-$0$ copy of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbf Z,\ker(q^m\cdot\mathrm{id}_{\mathcal G}))$ in which $r\in\mathbf T$ acts by the map induced by $\rho r$ on that kernel, the localisation of this $H^1$ at the complement of $\mathfrak P$ is additively isomorphic to $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbf Z,\mathcal J)$.
--
--   This is the formal counterpart of Mazur's construction of the $\mathfrak P$-primary Hopf orders attached to the $q^m$-torsion of the Néron identity component of $J_0(p)$, together with the comparison of the $\mathfrak P$-localised fppf $H^1$ of the $q^m$-torsion sheaf with the $H^1$ of the sheaf of points of the Hopf order. It is used in the construction of the Eisenstein-primary torsion core of $J_0(p)$ via [`ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd`](thm.html#ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronIdentityComponent_exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv.lean

import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroTorsionHopfOrder
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.exists_jZeroTorsionHopfOrder_forall_nonempty_localizedModule_fppfCohomology_kernel_addEquiv
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hqn : q ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (N : JZeroNeronIdentityComponent p) (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = N.L.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (ρ : letI := heckeModuleBar p; HeckeAlg →+* End 𝒢)
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver N.g N.g,
        (∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φ.1) ∧
        ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U ((ρ t).1.app (op U) s)).1 = (e U s).1 ≫ φ.1) :
    letI := heckeModuleBar p
    ∃ C : JZeroTorsionHopfOrder p q A hA (fun m => eisensteinPrimaryTorsionBar p q m),
      ∀ (m : ℕ) (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
        (e𝒥 : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (C.H m →ₐ[ℤ] Γ(U.left, ⊤))))
        (_ : ∀ {U W : specInt.Fppf} (f : U ⟶ W) (s : 𝒥.1.obj (op W)) (h : C.H m),
          (Additive.toMul (e𝒥 U (𝒥.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (e𝒥 W s)) h))
        [Small.{0} (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1)]
        (inst : Module HeckeAlg (Shrink.{0} (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1)))
        (_ : letI := inst
          ∀ r : HeckeAlg, ∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ r = ρ r ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
            ∀ y : fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1,
              r • equivShrink (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1) y =
                equivShrink (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1)
                  (fppfCohomologyMap specInt (kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ r) (ρ r) w) 1 y)),
        letI := inst
        Nonempty (LocalizedModule (eisensteinMaximalIdeal p q).primeCompl
            (Shrink.{0} (fppfCohomology specInt (kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) 1))
          ≃+ fppfCohomology specInt 𝒥 1) := by sorry
