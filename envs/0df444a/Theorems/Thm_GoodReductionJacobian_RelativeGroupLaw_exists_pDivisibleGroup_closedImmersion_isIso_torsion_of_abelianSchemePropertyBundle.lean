-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_abelianSchemePropertyBundle
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/fcb8757b-ed40-5ec5-8975-d05ea59f288d
-- title:
--   The p-divisible group of an abelian scheme: height 2d
-- statement:
--   Let $R$ be a Noetherian local commutative ring, let $f \colon J \to \operatorname{Spec} R$ be a morphism of schemes, and let $L$ be a relative group law on $f$, i.e. a functorial group structure $(\mathrm{mul}, \mathrm{one}, \mathrm{inv})$ on the sets of sections $\{\varphi \colon T \to J \mid \varphi \circ f = t\}$ for all $t \colon T \to \operatorname{Spec} R$, compatible with base change along $\psi \colon T' \to T$. Assume `AbelianSchemePropertyBundle R f`, namely that $f$ is smooth and proper with connected fibres and admits some relative group law; assume $L$ is commutative, that $f$ is smooth of relative dimension $d$, let $p$ be a prime, and let $\Omega$ be an algebraically closed field of characteristic $0$ with an $R$-algebra structure. Then there is a $p$-divisible group $G$ over $R$ of height $2d$ — a system of finite free $R$-algebras $G.\mathrm{level}\,v$, each a cocommutative Hopf algebra of rank $p^{v\cdot 2d}$, with surjective bialgebra transition maps whose kernels are the $p^v$-torsion ideals — which has dimension $d$ in the sense that each cotangent module $G.\mathrm{Cotangent}\,v$ is isomorphic to $(R/p^vR)^d$, together with an additive map $\iota_G$ from $G.\mathrm{Points}\,\Omega$ (the direct limit of the convolution groups of $R$-algebra maps $G.\mathrm{level}\,v \to \Omega$) to $L.\mathrm{AlgPoints}$ over $\Omega$ (the group of $\Omega$-sections of $f$ under $L.\mathrm{mul}$), and morphisms $\iota_v \colon \operatorname{Spec}(G.\mathrm{level}\,v) \to J$, such that: $\iota_G$ is injective; $\iota_G$ commutes with the action of every $\sigma \in \mathrm{Aut}_R(\Omega)$; every element of $L.\mathrm{AlgPoints}$ killed by some $p^n$ lies in the range of $\iota_G$; each $\iota_v$ followed by $f$ is the structure morphism $\operatorname{Spec}$ of $R \to G.\mathrm{level}\,v$; each $\iota_v$ is a closed immersion; $\iota_v$ followed by the multiplication-by-$p^v$ endomorphism $L.\mathrm{schemeNsmul}(p^v)$ equals the unit section composed with the structure morphism; $\iota_G$ on the level-$v$ points is computed by composing $\operatorname{Spec}$ of the corresponding $R$-algebra map $G.\mathrm{level}\,v \to \Omega$ with $\iota_v$; for every $R$-algebra $B$ and level-$v$ $B$-points $x,y$ whose associated morphisms lie over $\operatorname{Spec} B$, the morphism attached to the convolution product $x \ast y$ is $L.\mathrm{mul}$ of those of $x$ and $y$; $\operatorname{Spec}$ of the transition map followed by $\iota_{v+1}$ equals $\iota_v$; every endomorphism $E$ of $J$ over $\operatorname{Spec} R$ that is multiplicative for $L.\mathrm{mul}$ on all sections is induced by a family of $R$-bialgebra endomorphisms $\varphi_v$ of $G.\mathrm{level}\,v$ compatible with the transitions, in the sense that $\operatorname{Spec}(\varphi_v)$ followed by $\iota_v$ equals $\iota_v$ followed by $E$; and finally, for each $v$, the morphism from $\operatorname{Spec}(G.\mathrm{level}\,v)$ into the fibre product of $L.\mathrm{schemeNsmul}(p^v)$ with the unit section, determined by $\iota_v$ and $\iota_v \circ f$, is an isomorphism, so that $\operatorname{Spec}(G.\mathrm{level}\,v)$ is identified with the kernel $J[p^v]$.
--
--   This is the statement that the $p$-power torsion of an abelian scheme over a Noetherian local ring forms a $p$-divisible group of height $2d$ and dimension $d$, whose level-$v$ piece is the finite flat group scheme $J[p^v]$, with the $\Omega$-points dictionary and the restriction of endomorphisms recorded as part of the package. It specialises the general packaging theorem for relative group laws by discharging its finiteness, flatness and torsion-counting hypotheses from the abelian-scheme properties, and is used in the Tate-module and Raynaud-quotient arguments for Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_abelianSchemePropertyBundle
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f) (hc : L.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω] :
    ∃ G : PDivisibleGroup R p (2 * d), G.HasDimension d ∧
      ∃ (ιG : G.Points Ω →+ L.AlgPoints hc Ω)
        (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J),

        Function.Injective ιG ∧
        (∀ (σ : Ω ≃ₐ[R] Ω) (x : G.Points Ω), ιG (σ • x) = σ • ιG x) ∧
        (∀ (e : L.AlgPoints hc Ω) (n : ℕ), ((p ^ n : ℕ) : ℤ) • e = 0 → e ∈ ιG.range) ∧

        (∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) ∧

        (∀ v : ℕ, IsClosedImmersion (ι v)) ∧

        (∀ v : ℕ, ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧

        (∀ (v : ℕ) (x : G.Point Ω v),
          (GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint (ιG (G.pointsMkAdd Ω v (Additive.ofMul x)))).1 =
            Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] Ω) : G.level v →+* Ω)) ≫ ι v) ∧

        (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
            Spec.map (CommRingCat.ofHom (algebraMap R B)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
            Spec.map (CommRingCat.ofHom (algebraMap R B))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
            (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

        (∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v) ∧

        (∀ (E : SchemeHomOver f f),
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
            NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
              L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
          ∃ φ : ∀ v : ℕ, G.level v →ₐc[R] G.level v,
            (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (G.transition v)) ∧
            ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : G.level v →+* G.level v)) ≫ ι v = ι v ≫ E.1) ∧

        (∀ (v : ℕ)
          (h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1),
          IsIso (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3)) := by sorry
