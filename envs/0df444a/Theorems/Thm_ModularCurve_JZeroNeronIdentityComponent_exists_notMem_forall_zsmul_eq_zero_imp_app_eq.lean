-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_notMem_forall_zsmul_eq_zero_imp_app_eq
-- name    : ModularCurve.JZeroNeronIdentityComponent.exists_notMem_forall_zsmul_eq_zero_imp_app_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/36e98e58-debe-56ed-a9d6-bf3215fa1259
-- title:
--   A Hecke element outside the Eisenstein ideal acting as t_m
-- statement:
--   Fix primes $p$ and $q$ and let $N$ be a `JZeroNeronIdentityComponent p`: a smooth, separated, surjective group scheme $G\to\operatorname{Spec}\mathbb Z$ with relative group law $L$, commutative and with flat surjective multiplication-by-$n$ maps, together with an additive, Galois- and Hecke-equivariant bijection `N.pts` from $JZero\,p$ (the degree-zero divisor class group of the modular function field at level $p$ over $\overline{\mathbb Q}$) onto the sections of $g$ over $\operatorname{Spec}\overline{\mathbb Q}$, plus the finite-index condition on sections. Let $\mathcal G$ be an abelian sheaf on the small fppf site of $\operatorname{Spec}\mathbb Z$, equipped with bijections $e_{\mathcal G}$ between $\mathcal G(U)$ and the morphisms $U\to G$ over $\operatorname{Spec}\mathbb Z$, for each fppf $U$, carrying addition to $L.\mathrm{mul}$ and restriction along $k\colon U\to V$ to precomposition with `k.left`; and let $\rho$ be a ring homomorphism from $\mathrm{HeckeAlg}=\mathbb Z[X_\ell:\ell\text{ prime}]$ to $\operatorname{End}\mathcal G$ such that every $t$ is realised by an endomorphism $\varphi$ of $G$ over $\mathbb Z$, acting on $JZero\,p$ through `N.pts` and on all sections by postcomposition. Fix $m$ with the $q^m$-torsion of $JZero\,p$ finite, and assume the kernel scheme $G[q^m]$, the pullback of $L.\mathrm{schemeNsmul}(q^m)$ along the identity section with structure morphism $\mathrm{pullback.fst}$ followed by $g$, is flat and locally of finite type over $\mathbb Z$. Let $t_m\in\mathrm{HeckeAlg}$, let $\varphi_t$ be an endomorphism of $G$ over $\mathbb Z$ and $e_K$ one of $G[q^m]$, subject to: for $x\in JZero\,p$ killed by $q^m$, $t_m\cdot x=x$ if and only if $x$ lies in `eisensteinPrimaryTorsionBar p q m`, the intersection of the kernel of multiplication by $q^m$ with the supremum over $k$ of the $(\mathfrak P^k)$-torsion submodules for $\mathfrak P=$ `eisensteinMaximalIdeal p q` (the preimage under `eisensteinEval p` of the ideal $(q)\subseteq\mathbb Z$); $e_K$ is idempotent; $t_m$ acts as postcomposition with $\varphi_t$ both on `N.pts` and on all sections of $\mathcal G$; and $e_K$ followed by $\mathrm{pullback.fst}$ equals $\mathrm{pullback.fst}$ followed by $\varphi_t$. The conclusion: there exists $s\in\mathrm{HeckeAlg}$ with $s\notin\mathfrak P$ such that $\rho(s)$ and $\rho(t_m)$ agree on every section $x\in\mathcal G(U)$, $U$ fppf over $\operatorname{Spec}\mathbb Z$, satisfying $q^m\cdot x=0$.
--
--   This is the step that replaces the Eisenstein projector $t_m$, whose behaviour depends on the level, by a single Hecke operator lying outside the Eisenstein maximal ideal $\mathfrak P$ and acting in the same way on all $q^m$-torsion sections of the points sheaf; the two cases are $t_m\notin\mathfrak P$, where $s=t_m$ serves, and $t_m\in\mathfrak P$, where the Eisenstein primary part vanishes and a suitable annihilator of the finite Hecke module $J_0(p)[q^m](\overline{\mathbb Q})$ is produced and compared with $t_m$ on the reduced scheme $G[q^m]$ by rigidity. It is used by [`ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector`](thm.html#ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronIdentityComponent_exists_notMem_forall_zsmul_eq_zero_imp_app_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.exists_notMem_forall_zsmul_eq_zero_imp_app_eq
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e𝒢 : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e𝒢 U (s + s') = N.L.mul U.hom (e𝒢 U s) (e𝒢 U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e𝒢 U (𝒢.1.map k.op s) = GoodReductionJacobian.schemeHomOverComp k.left (MorphismProperty.Over.w k) (e𝒢 V s))
    (ρ : letI := heckeModuleBar p; HeckeAlg →+* End 𝒢)
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver N.g N.g,
        (∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φ.1) ∧
        ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e𝒢 U ((ρ t).1.app (op U) s)).1 = (e𝒢 U s).1 ≫ φ.1)
    (m : ℕ) (hfin : Finite ↥(jZeroTorsion p (q ^ m)))
    [Flat (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)] [LocallyOfFiniteType (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)]
    (tm : letI := heckeModuleBar p; HeckeAlg) (φt : SchemeHomOver N.g N.g)
    (eK : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (ht : letI := heckeModuleBar p
      ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → (tm • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (heK_idem : eK.1 ≫ eK.1 = eK.1)
    (hφt_pts : letI := heckeModuleBar p; ∀ x : JZero p, (N.pts (tm • x)).1 = (N.pts x).1 ≫ φt.1)
    (hφt_sec : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e𝒢 U ((ρ tm).1.app (op U) s)).1 = (e𝒢 U s).1 ≫ φt.1)
    (heφ : eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1) :
    letI := heckeModuleBar p
    ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧
      ∀ (U : specInt.Fppf) (x : 𝒢.1.obj (op U)), ((q : ℤ) ^ m) • x = 0 →
        (ρ s).1.app (op U) x = (ρ tm).1.app (op U) x := by sorry
