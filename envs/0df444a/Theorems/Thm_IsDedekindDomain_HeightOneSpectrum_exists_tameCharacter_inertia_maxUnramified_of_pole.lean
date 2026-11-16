-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_tameCharacter_inertia_maxUnramified_of_pole
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_tameCharacter_inertia_maxUnramified_of_pole
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:05:57.950464+00:00
-- url     : https://prove2.me/theorems/bb542dca-ec8b-44f9-90fd-da8f90ac7856
-- title:
--   Tame inertia at a boundary place in the maximal extension unramified over $A$: $\mathrm{Hom}_{\mathrm{cont}}(I(\mathfrak{Q}), M) \cong M(-1)$
-- statement:
--   Let $K$ be a field of characteristic $p > 0$, let $A \subset K$ be a domain with fraction field $K$ (for instance the coordinate ring of an affine curve $U = \mathrm{Spec}\,A$ over a finite field $\mathbb{F}_q$), and let $R_0 \subset K$ be a Dedekind domain with fraction field $K$ such that $R_0/J$ is finite for every nonzero ideal $J$. Fix an algebraic closure $\overline{K}$ and let $K_U \subset \overline{K}$ be the compositum of all finite Galois extensions $L/K$ in $\overline{K}$ that are unramified over $A$: for every prime $\mathfrak{P}$ of the integral closure $A_L$ of $A$ in $L$, the only $\sigma \in \mathrm{Gal}(L/K)$ with $\sigma(b) \equiv b \pmod{\mathfrak{P}}$ for all $b \in A_L$ is $\sigma = 1$. Thus $\mathrm{Gal}(K_U/K)$, with its Krull topology, is the fundamental group $\pi_1(U)$.
--
--   Let $\mathfrak{Q}$ be a nonzero prime of the integral closure $R_{0,U}$ of $R_0$ in $K_U$, let $x = \mathfrak{Q} \cap R_0$ be the place of $K$ below it, and assume that $x$ lies at the boundary of $U$: some $a \in A$ has a pole at $x$, i.e. $|a|_x > 1$. Let
--
--   $$I = I(\mathfrak{Q}) = \{\sigma \in \mathrm{Gal}(K_U/K) : \sigma(b) \equiv b \pmod{\mathfrak{Q}} \text{ for all } b \in R_{0,U}\}$$
--
--   be the inertia group of $\mathfrak{Q}$, let $N \ge 1$ be an integer invertible in $A$ and in $R_0$, and let $\zeta \in K_U$ be a primitive $N$-th root of unity fixed by $I$. Then there exist a continuous (that is, locally constant) homomorphism $\theta : I \to \mathbb{Z}/N\mathbb{Z}$ and an element $\sigma_0 \in I$ with $\theta(\sigma_0) = 1$ such that:
--
--   1. for every $\varphi$ in the decomposition group $D(\mathfrak{Q}) = \{\varphi \in \mathrm{Gal}(K_U/K) : \varphi(\mathfrak{Q}) = \mathfrak{Q}\}$ and every $w \in \mathbb{Z}/N\mathbb{Z}$ with $\varphi(\zeta) = \zeta^{w}$,
--
--   $$\theta(\varphi\,\tau\,\varphi^{-1}) = w\,\theta(\tau) \qquad \text{for all } \tau \in I;$$
--
--   2. for every abelian group $M$ with $N M = 0$, every continuous homomorphism $\chi : I \to M$ ($M$ discrete) satisfies $\chi(\sigma) = \theta(\sigma)\,\chi(\sigma_0)$ for all $\sigma \in I$, and conversely, for every $m \in M$ the map $\sigma \mapsto \theta(\sigma)\,m$ is a continuous homomorphism $I \to M$ taking the value $m$ at $\sigma_0$.
--
--   Hence $\chi \mapsto \chi(\sigma_0)$ is a bijection
--
--   $$\mathrm{Hom}_{\mathrm{cont}}(I(\mathfrak{Q}), M) \xrightarrow{\ \sim\ } M(-1),$$
--
--   which intertwines the conjugation action of $D(\mathfrak{Q})$ with its action on $M(-1) = \mathrm{Hom}(\mu_N, M)$ through the inverse of the cyclotomic character: the largest quotient of exponent $N$ of the abelianised inertia group at a boundary place of $U$ is $\mu_N \cong (\mathbb{Z}/N\mathbb{Z})(1)$.
--
--   This is the global, function-field form of the structure of tame inertia of a local field (the tame inertia group is $\prod_{\ell \ne p} \mathbb{Z}_\ell(1)$): inside $\pi_1(U)$ the inertia groups at the points at infinity of $U$ have exactly the expected prime-to-$p$ abelian quotients, with the expected Galois twist. It is the local input that computes $H^1(I(\mathfrak{Q}), M)$ for tame coefficients at the missing points of an affine curve, as used in the cohomology with compact support of curves over finite fields and in the Grothendieck–Ogg–Shafarevich formula.
--
--   **Formalization Note**: $\overline{K}$ is `AlgebraicClosure K` and $K_U$ is a variable `KU : IntermediateField K (AlgebraicClosure K)` with defining equation `hKU`, an `iSup` over the intermediate fields `L` with `FiniteDimensional K L`, `IsGalois K L` and the unramifiedness condition; $A_L$ is `integralClosure A L` and $R_{0,U}$ is `integralClosure R0 KU`. The congruence $\sigma(b) \equiv b \pmod{\mathfrak{P}}$ is written elementwise as `∃ c ∈ P, (c : L) = σ b - b`, both in the unramifiedness condition and in the membership criterion `hI` for the inertia group, which is a variable `I : Subgroup (KU ≃ₐ[K] KU)`. $\mathrm{Gal}(K_U/K)$ is `KU ≃ₐ[K] KU` with Mathlib's Krull topology instance; continuity of maps to the discrete groups $\mathbb{Z}/N\mathbb{Z}$ (`ZMod N`) and $M$ is `IsLocallyConstant`, and the homomorphism property is written `θ (σ * τ) = θ σ + θ τ`. The decomposition group condition on $\varphi$ is `∀ b, (∃ c ∈ Q, (c : KU) = φ b) ↔ b ∈ Q`, $\zeta^{w}$ is `ζ ^ w.val`, and item 1 is stated for $\sigma, \tau \in I$ with `τ = φ⁻¹ * σ * φ` as `θ σ = w * θ τ`. The multiple $\theta(\sigma)\,m$ is `(θ σ).val • m` and $N M = 0$ is `∀ m : M, N • m = 0`. The place $x$ is `x : IsDedekindDomain.HeightOneSpectrum R0` with `x.asIdeal = Q.comap (algebraMap R0 (integralClosure R0 KU))`, and the pole condition is `1 < x.valuation K (algebraMap A K a)` (Mathlib's multiplicative $x$-adic valuation, which is $\le 1$ exactly on the local ring at $x$). Finiteness of the quotients of $R_0$ is `Ring.HasFiniteQuotients R0`; $N \ge 1$ is `[NeZero N]` and its invertibility is `IsUnit (N : A)`, `IsUnit (N : R0)`. The hypotheses are satisfiable: take $A = \mathbb{F}_q[t]$, $K = \mathbb{F}_q(t)$, $R_0 = \mathbb{F}_q[1/t]$, $a = t$ (a pole at $x = (1/t)$), any $N$ prime to $p$, $\zeta \in K_U$ a primitive $N$-th root of unity (constant field extensions are unramified everywhere, so $\zeta \in K_U$ and $I$ fixes $\zeta$), and $\mathfrak{Q}$ any prime of $R_{0,U}$ lying over $x$ (it is nonzero because $x \ne 0$).
-- source:
--   A. Grothendieck, Revêtements étales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Exposé XIII §5; A. Grothendieck and J. P. Murre, The Tame Fundamental Group of a Formal Neighbourhood of a Divisor with Normal Crossings on a Scheme, Lecture Notes in Math. 208, Springer (1971); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter IV §2 (structure of tame inertia); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter I §5

import Mathlib

set_option autoImplicit false

theorem IsDedekindDomain.HeightOneSpectrum.exists_tameCharacter_inertia_maxUnramified_of_pole
    (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (R0 : Type) [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]
    [Ring.HasFiniteQuotients R0] (p : ℕ) [Fact p.Prime] [CharP K p]
    (KU : IntermediateField K (AlgebraicClosure K))
    (hKU : KU = ⨆ L : {L : IntermediateField K (AlgebraicClosure K) //
        FiniteDimensional K L ∧ IsGalois K L ∧
        ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
          (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1}, L.1)
    (Q : Ideal (integralClosure R0 KU)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (I : Subgroup (KU ≃ₐ[K] KU))
    (hI : ∀ σ : KU ≃ₐ[K] KU, σ ∈ I ↔ ∀ b : integralClosure R0 KU, ∃ c ∈ Q, (c : KU) = σ b - b)
    (N : ℕ) [NeZero N] (hNA : IsUnit (N : A)) (hNR : IsUnit (N : R0))
    (ζ : KU) (hζ : IsPrimitiveRoot ζ N) (hζI : ∀ σ ∈ I, σ ζ = ζ)
    (x : IsDedekindDomain.HeightOneSpectrum R0)
    (hx : x.asIdeal = Q.comap (algebraMap R0 (integralClosure R0 KU)))
    (a : A) (ha : 1 < x.valuation K (algebraMap A K a)) :
    ∃ θ : I → ZMod N, ∃ σ₀ : I,
      IsLocallyConstant θ ∧ (∀ σ τ : I, θ (σ * τ) = θ σ + θ τ) ∧ θ σ₀ = 1 ∧
      (∀ φ : KU ≃ₐ[K] KU, (∀ b : integralClosure R0 KU, (∃ c ∈ Q, (c : KU) = φ b) ↔ b ∈ Q) →
        ∀ w : ZMod N, φ ζ = ζ ^ w.val →
        ∀ σ τ : I, (τ : KU ≃ₐ[K] KU) = φ⁻¹ * σ * φ → θ σ = w * θ τ) ∧
      ∀ (M : Type) [AddCommGroup M], (∀ m : M, N • m = 0) →
        (∀ χ : I → M, IsLocallyConstant χ → (∀ σ τ : I, χ (σ * τ) = χ σ + χ τ) →
          ∀ σ : I, χ σ = (θ σ).val • χ σ₀) ∧
        ∀ m : M, IsLocallyConstant (fun σ : I => (θ σ).val • m) ∧
          (∀ σ τ : I, (θ (σ * τ)).val • m = (θ σ).val • m + (θ τ).val • m) ∧
          (θ σ₀).val • m = m := by sorry
