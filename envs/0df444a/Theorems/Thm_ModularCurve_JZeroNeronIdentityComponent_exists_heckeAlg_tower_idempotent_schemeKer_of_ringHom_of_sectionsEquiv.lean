-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
-- name    : ModularCurve.JZeroNeronIdentityComponent.exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/319bdadc-52fc-5842-b280-41b956d5a1c7
-- title:
--   Eisenstein idempotents on the q^m-torsion kernel schemes
-- statement:
--   Let $p,q$ be primes and let $N$ be a `JZeroNeronIdentityComponent p`, i.e. a smooth, separated, surjective scheme $G\to\operatorname{Spec}\mathbb Z$ with connected fibres carrying a commutative relative group law $L$, a group isomorphism `N.pts` from $J:=$ `JZero p` $=\mathrm{Pic}^0$ of the level-$p$ modular function field over $\overline{\mathbb Q}$ onto the $\overline{\mathbb Q}$-sections of $g$, Galois and Hecke equivariance, and flatness and surjectivity of the multiplication morphisms `N.L.schemeNsmul n`. Let $\mathcal G$ be an abelian sheaf on the small fppf site of $\operatorname{Spec}\mathbb Z$ together with bijections $e_U\colon\mathcal G(U)\to\{\varphi\colon U\to G\mid \varphi\circ g=U.\mathrm{hom}\}$ that carry addition to $L$ and are natural in $U$, and let $\rho\colon$ `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]\to\operatorname{End}\mathcal G$ be a ring homomorphism such that every $t$ acts, both on `N.pts` and on $\mathcal G$ via $e$, by postcomposition with a single endomorphism of $G$ over $\mathbb Z$. Assume each $q^m$-torsion subgroup of $J$ is finite. Then there are $t\colon\mathbb N\to$ `HeckeAlg`, endomorphisms $\varphi_m$ of $G$ over $\mathbb Z$, and endomorphisms $e_m$ of the kernel scheme $G[q^m]$, the pullback of `N.L.schemeNsmul (q ^ m)` along the unit section with structure morphism $\mathrm{pr}_1$ followed by $g$, such that: on $J[q^m]$, $t_m$ is idempotent, fixes exactly `eisensteinPrimaryTorsionBar p q m` (the $q^m$-torsion intersected with the union of the submodules killed by powers of the Eisenstein maximal ideal at $q$), and $t_{m+1}=t_m$; on $q^m$-torsion sections of $\mathcal G$ over any $U$, $\rho(t_m)$ is idempotent and $\rho(t_{m+1})=\rho(t_m)$; and for each $m$, $e_m\circ e_m=e_m$, $\varphi_m$ realises $t_m$ on $J$ and $\rho(t_m)$ on $\mathcal G$, $\mathrm{pr}_1\circ e_m=\varphi_m\circ\mathrm{pr}_1$, $\varphi_{m+1}\circ\mathrm{pr}_1=\varphi_m\circ\mathrm{pr}_1$, and $e_m$ is a homomorphism for every relative group law $L_K$ on $G[q^m]$ over $\mathbb Z$ for which $\mathrm{pr}_1$ is a homomorphism to $(G,L)$.
--
--   This packages Mazur's Eisenstein-primary projectors on the $q$-power torsion of $J_0(p)$ in three compatible forms: as a tower of Hecke elements acting on $\overline{\mathbb Q}$-points, as idempotent endomorphisms of the fppf points sheaf on $q^m$-torsion sections, and as genuine group-scheme idempotents on the kernel schemes $G[q^m]$ over $\mathbb Z$, with compatibility as $m$ grows. It is used to cut out the Eisenstein part in the construction of the points embeddings of the primary torsion core and in the Hopf-order/fppf-cohomology comparison for $q^m$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronIdentityComponent_exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv.lean

import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = N.L.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (ρ : HeckeAlg →+* End 𝒢)
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver N.g N.g,
        (∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φ.1) ∧
        ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U ((ρ t).1.app (op U) s)).1 = (e U s).1 ≫ φ.1)
    (hfin : ∀ m : ℕ, Finite ↥(jZeroTorsion p (q ^ m))) :
    letI := heckeModuleBar p
    ∃ (t : ℕ → HeckeAlg) (φ : ℕ → SchemeHomOver N.g N.g)
      (eK : ∀ m : ℕ, SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),

      (∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 →
        t m • (t m • x) = t m • x ∧ (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m) ∧
          t (m + 1) • x = t m • x) ∧

      (∀ (m : ℕ) (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (q ^ m : ℤ) • s = 0 →
        (ρ (t m)).1.app (op U) ((ρ (t m)).1.app (op U) s) = (ρ (t m)).1.app (op U) s ∧
        (ρ (t (m + 1))).1.app (op U) s = (ρ (t m)).1.app (op U) s) ∧

      (∀ m : ℕ,
        (eK m).1 ≫ (eK m).1 = (eK m).1 ∧
        (∀ x : JZero p, (N.pts (t m • x)).1 = (N.pts x).1 ≫ (φ m).1) ∧
        (∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U ((ρ (t m)).1.app (op U) s)).1 = (e U s).1 ≫ (φ m).1) ∧
        (eK m).1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φ m).1 ∧
        pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φ (m + 1)).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φ m).1 ∧
        (∀ (LK : RelativeGroupLaw ℤ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
            NeronModelInfra.schemeHomOverComp (LK.mul s x y)
                (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g) =
              N.L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)
                (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
          ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
            NeronModelInfra.schemeHomOverComp (LK.mul s x y) (eK m) =
              LK.mul s (NeronModelInfra.schemeHomOverComp x (eK m)) (NeronModelInfra.schemeHomOverComp y (eK m)))) := by sorry
