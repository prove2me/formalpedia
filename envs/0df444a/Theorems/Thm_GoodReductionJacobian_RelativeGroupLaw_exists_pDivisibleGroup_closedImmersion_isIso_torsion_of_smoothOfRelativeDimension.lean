-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/41783b34-7e05-5bdb-a296-4f1c412e32c4
-- title:
--   The p-divisible group of a smooth relative group law, scheme-theoretically
-- statement:
--   Let $R$ be a local commutative ring, $J$ a scheme and $f \colon J \to \operatorname{Spec} R$ a separated morphism, smooth of relative dimension $d$, carrying a relative group law $L$ (a group structure on each set $\{\varphi : T \to J \mid \varphi \circ f = t\}$ of points over a base morphism $t \colon T \to \operatorname{Spec} R$, natural in $T$), assumed commutative. Let $p,h \in \mathbb{N}$ and suppose that for every $v$ the morphism $[p^v] \colon J \to J$ obtained by iterating the group law on the identity point is finite and flat. Let $\Omega$ be an algebraically closed field of characteristic $0$ which is an $R$-algebra, and suppose that the subgroup of elements killed by $p^v$ in the additive group $J(\Omega) = \{\varphi : \operatorname{Spec}\Omega \to J$ over $\operatorname{Spec} R\}$ has cardinality $p^{vh}$ for every $v$. Then there is a $p$-divisible group $G$ over $R$ of height $h$ — a system of finite free $R$-Hopf algebras $G_v$ with cocommutative comultiplication, $\operatorname{rank}_R G_v = p^{vh}$, and surjective bialgebra transitions $G_{v+1} \to G_v$ with kernel the $p^v$-torsion ideal — such that each cotangent module $(\mathfrak{a}_v)_{\mathrm{cot}}$ of $G$ at level $v$ is $R$-linearly isomorphic to $(R/p^vR)^d$, together with an additive map $\iota_G \colon G(\Omega) \to J(\Omega)$ (on the direct limit of the convolution groups $\operatorname{Hom}_{R\text{-alg}}(G_v,\Omega)$) and morphisms $\iota_v \colon \operatorname{Spec} G_v \to J$ satisfying: $\iota_G$ is injective, commutes with the action of $\operatorname{Aut}_R(\Omega)$, and its image contains every element of $J(\Omega)$ of $p$-power order; $\iota_v$ followed by $f$ is $\operatorname{Spec}$ of the structure map $R \to G_v$; $\iota_v$ is a closed immersion; $\iota_v$ followed by $[p^v]$ is $\iota_v \circ f$ followed by the unit section; for an $\Omega$-point $x$ of level $v$, the point $\iota_G$ of the class of $x$ is $\operatorname{Spec}(x)$ followed by $\iota_v$; for every $R$-algebra $B$ and $B$-points $x,y$ of level $v$ whose associated morphisms lie over $\operatorname{Spec} B$, the morphism attached to the convolution product $x y$ is the $L$-product of those attached to $x$ and $y$; $\operatorname{Spec}$ of the transition $G_{v+1} \to G_v$ followed by $\iota_{v+1}$ equals $\iota_v$; every endomorphism $E$ of $J$ over $\operatorname{Spec} R$ that is compatible with the group law at all bases is induced by a family of $R$-bialgebra endomorphisms $\varphi_v$ of $G_v$ commuting with the transitions, in the sense that $\operatorname{Spec}(\varphi_v)$ followed by $\iota_v$ equals $\iota_v$ followed by $E$; and, for each $v$, the morphism from $\operatorname{Spec} G_v$ to the fibre product of $[p^v]$ and the unit section determined by $\iota_v$ and $\iota_v \circ f$ is an isomorphism.
--
--   This is the scheme-theoretic form of Tate's construction of the $p$-divisible group attached to a smooth commutative group scheme with finite flat $p$-power torsion over a local base: the levels are realised, via the $\iota_v$, as closed subgroup schemes identified with the kernels $J[p^v]$, and endomorphisms of $J$ over the base act on the system. It is used to derive the corresponding statement for a Jacobian packaged through an abelian-scheme property bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_smoothOfRelativeDimension
    {R : Type} [CommRing R] [IsLocalRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f]
    (p h : ℕ)
    (hfin : ∀ v : ℕ, IsFinite (L.schemeNsmul (p ^ v)))
    (hflat : ∀ v : ℕ, Flat (L.schemeNsmul (p ^ v)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω]
    (hcard : ∀ v : ℕ,
      Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) ((p ^ v : ℕ) : ℤ)) = p ^ (v * h)) :
    ∃ G : PDivisibleGroup R p h, G.HasDimension d ∧
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
