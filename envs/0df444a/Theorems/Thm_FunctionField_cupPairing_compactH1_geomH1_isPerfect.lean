-- Prove2me | Theorems.Thm_FunctionField_cupPairing_compactH1_geomH1_isPerfect
-- name    : FunctionField.cupPairing_compactH1_geomH1_isPerfect
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-25T14:30:06.760385+00:00
-- url     : https://prove2.me/theorems/0fcbc32b-f79e-5304-a2b4-24df2e652091
-- title:
--   Poincaré duality on an affine curve over $\overline{\mathbb F}_q$ (unconditional): $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ is perfect, Frobenius factor $q\,\sigma(\varphi^{-1})$
-- statement:
--   Let $\mathbb F_q$ be a finite field of characteristic $p$ with $q$ elements, and let $F$ be a function field over $\mathbb F_q$ (a finite separable extension of $\mathbb F_q(t)$) whose constant field is exactly $\mathbb F_q$. Let $A\subset F$ be the integral closure of $\mathbb F_q[t]$, so that $U=\operatorname{Spec}A$ is the smooth affine curve obtained from the complete curve $X$ of $F$ by removing the places over $t=\infty$, and let $R_\infty\subset F$ be the integral closure of the valuation ring of $\mathbb F_q(t)$ at infinity. Fix an algebraic closure $\overline F$ and let $K_U\subset\overline F$ be the compositum of all finite Galois extensions $L/F$ in $\overline F$ that are unramified over $A$: for every prime $\mathfrak P$ of the integral closure $A_L$ of $A$ in $L$, the only $g\in\mathrm{Gal}(L/F)$ with $g(b)\equiv b\pmod{\mathfrak P}$ for all $b\in A_L$ is $g=1$. Thus $\mathrm{Gal}(K_U/F)$ with its Krull topology is $\pi_1(U)$, and
--   $$\Gamma=\{g\in\mathrm{Gal}(K_U/F):\ g(x)=x\text{ for every }x\in K_U\text{ with }x^{q^k}=x\text{ for some }k\ge1\}=\mathrm{Gal}(K_U/F\overline{\mathbb F}_q)$$
--   is the geometric fundamental group $\pi_1(\bar U)$.
--
--   The nonzero primes of the integral closure $R_{\infty,U}$ of $R_\infty$ in $K_U$ are the places of $K_U$ over the points at infinity. Let $S$ be a finite nonempty set and $\mathfrak P_s$ ($s\in S$) nonzero primes of $R_{\infty,U}$ forming a system of representatives of these primes modulo $\Gamma$ (every one is $g(\mathfrak P_s)$ for some $s$ and $g\in\Gamma$, and $g(\mathfrak P_s)=\mathfrak P_{s'}$ with $g\in\Gamma$ forces $s=s'$); so $S$ is the set of points of $\bar X\setminus\bar U$. Let $I_s=\{g:\ g(b)\equiv b\pmod{\mathfrak P_s}\text{ for all }b\in R_{\infty,U}\}$ be the inertia group of $\mathfrak P_s$.
--
--   Let $\ell\ne p$ be a prime, $n\ge0$, $\Lambda$ a finite commutative ring with $\ell^n\Lambda=0$, and $\sigma$ a continuous action of $\mathrm{Gal}(K_U/F)$ on $\Lambda$ by $\Lambda$-linear maps (a continuous character with values in $\Lambda^\times$) that is trivial on $\Gamma$.
--
--   In cochain form $H^1(\bar U,\sigma)=\operatorname{Hom}_{\rm cont}(\Gamma,\Lambda)$ (as $\sigma|_\Gamma$ is trivial), and $H^1_c(\bar U,\Lambda)$ is the first cohomology of the cone of restriction to the boundary: pairs $(c,m)$ with $c\in\operatorname{Hom}_{\rm cont}(\Gamma,\Lambda)$ vanishing on every $\Gamma\cap I_s$ and $m\in\Lambda^S$, modulo the pairs $(0,\text{constant})$. Then there are $t_s\in\Gamma\cap I_s$ such that:
--
--   1. for all $c,d\in\operatorname{Hom}_{\rm cont}(\Gamma,\Lambda)$ the $2$-cocycle $c\cup d$ is a coboundary: $c(g)\,d(h)=u(h)-u(gh)+u(g)$ for some locally constant $u:\Gamma\to\Lambda$;
--   2. the pairing
--   $$\langle (c,m),d\rangle=\sum_{s\in S}\big(m_s\,d(t_s)-u(t_s)\big),$$
--   with $u$ any such primitive of $c\cup d$, is well defined, its left kernel is exactly $\{(0,\text{constant})\}$, its right kernel is $0$, and every $\Lambda$-linear functional on either side (vanishing on $\{(0,\text{constant})\}$ for the left side) is of the form $\langle x,\cdot\rangle$, respectively $\langle\cdot,d\rangle$: the pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ is perfect;
--   3. for every $\varphi\in\mathrm{Gal}(K_U/F)$ acting by $x\mapsto x^q$ on the constants there are $\tau:S\to S$ and $\eta_s\in\Gamma$ with $\varphi(\mathfrak P_s)=\eta_s(\mathfrak P_{\tau(s)})$, such that the Frobenius twists $F(c,m)=\big(g\mapsto c(\varphi g\varphi^{-1}),\ s\mapsto m_{\tau(s)}-c(\eta_s)\big)$ and $F d=\big(g\mapsto\sigma(\varphi^{-1})\,d(\varphi g\varphi^{-1})\big)$ are again cocycles and
--   $$\langle F x,F d\rangle=q\,\sigma(\varphi^{-1})(1)\,\langle x,d\rangle .$$
--
--   Role: Poincaré duality for the cohomology in degree $1$ of a curve over $\overline{\mathbb F}_q$ with constant (or $\Gamma$-trivial) coefficients, $H^1_c(\bar U,\Lambda)\cong\operatorname{Hom}(H^1(\bar U,\Lambda),\Lambda)(-1)$, written entirely in terms of continuous cochains of the Galois group of the maximal extension unramified over $U$; the factor $q$ in item 3 is the Tate twist $H^2_c(\bar U,\Lambda)\cong\Lambda(-1)$. This is the unconditional form of `FunctionField.cupPairing_compactH1_geomH1_isPerfect_of_picDivisible`: its two hypotheses, the $\ell$-divisibility of $\operatorname{Pic}(\bar U)$ and the $\ell^n$-divisibility of $\operatorname{Pic}^0(\bar X)=J(\overline{\mathbb F}_q)$, hold for every curve when $\ell\ne p$ (`FunctionField.geomPic_affine_divisible_and_geomPic0_divisible`).
--
--   **Formalization Note**: $\overline F$ is `AlgebraicClosure F`; $A$ is `FunctionField.ringOfIntegers Fq F` and $R_\infty$ is `integralClosure (RatFunc.inftyValuation Fq).valuationSubring F`; integral closures in intermediate fields are `integralClosure _ M`. The constant field condition is `algebraicClosure Fq F = ⊥`. $K_U$, the constant field levels $F\mathbb F_{p^m}$ (`CL m`, the adjunction of the roots of $X^{p^m}-X$), $\Gamma$ and the inertia groups $I_s$ are variables with defining equations `hKU`, `hCL`, `hΓ`, `hI`; congruences mod a prime are written elementwise (`∃ c ∈ P, (c : L) = g b - b`), and $g(\mathfrak P)$ is described by `b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g c`. $\mathrm{Gal}(K_U/F)$ is `KU ≃ₐ[F] KU` with Mathlib's Krull topology; continuity of maps $\Gamma\to\Lambda$ is `IsLocallyConstant`, the character $\sigma$ is a `Representation Λ (KU ≃ₐ[F] KU) Λ` with open kernel, and $\ell^n\Lambda=0$ is `((l ^ n : ℕ) : Λ) = 0` with $\ell\ne p$ as `(l : F) ≠ 0`. Cochains are plain functions; an element of $H^1_c$ is represented by `x : (Γ → Λ) × (S → Λ)` satisfying the cocycle conditions, the pairing is a function `pair` on representatives given by the formula of item 2 for every primitive `u`, and perfectness is stated elementwise (kernels and representability of additive, $\Lambda$-homogeneous functionals). The hypotheses are satisfiable, for example by $F=\mathbb F_q(t)$, where $U=\mathbb A^1$ and $S$ is a single point, with $\Lambda=\mathbb Z/\ell$ and $\sigma$ trivial.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib

set_option autoImplicit false

theorem FunctionField.cupPairing_compactH1_geomH1_isPerfect
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hk : algebraicClosure Fq F = ⊥)
    (l : ℕ) [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (CL : ℕ → IntermediateField F (AlgebraicClosure F))
    (hCL : ∀ m, CL m = IntermediateField.adjoin F
      (((Polynomial.X : Polynomial F) ^ (p ^ m) - Polynomial.X).rootSet (AlgebraicClosure F)))
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[F] KU))
    (hΓ : ∀ g : KU ≃ₐ[F] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (P : S → Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU))
    (hP : ∀ s, (P s).IsPrime ∧ P s ≠ ⊥)
    (hcover : ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
      Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
        ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU))
    (hdisj : ∀ s s', ∀ g ∈ Γ,
      (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s')
    (I : S → Subgroup (KU ≃ₐ[F] KU))
    (hI : ∀ s (g : KU ≃ₐ[F] KU), g ∈ I s ↔
      ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, ∃ c ∈ P s, (c : KU) = g (b : KU) - b)
    (Λ : Type) [CommRing Λ] [Finite Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (σ : Representation Λ (KU ≃ₐ[F] KU) Λ) (hσ : IsOpen (σ.ker : Set (KU ≃ₐ[F] KU)))
    (htriv : ∀ g ∈ Γ, ∀ x : Λ, σ g x = x) :
    ∃ t : S → Γ, (∀ s, (t s : KU ≃ₐ[F] KU) ∈ I s) ∧
      (∀ c d : Γ → Λ, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + c h) →
        (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
        ∃ u : Γ → Λ, IsLocallyConstant u ∧ ∀ g h, c g * d h = u h - u (g * h) + u g) ∧
      ∃ pair : (Γ → Λ) × (S → Λ) → (Γ → Λ) → Λ,
        (∀ (x : (Γ → Λ) × (S → Λ)) (d u : Γ → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
          (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
          (IsLocallyConstant u ∧ ∀ g h, x.1 g * d h = u h - u (g * h) + u g) →
          pair x d = ∑ s, (x.2 s * d (t s) - u (t s))) ∧
        (∀ x : (Γ → Λ) × (S → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
          (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → pair x d = 0) →
          x.1 = 0 ∧ ∃ a : Λ, ∀ s, x.2 s = a) ∧
        (∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
          (∀ x : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → pair x d = 0) →
          d = 0) ∧
        (∀ f : (Γ → Λ) → Λ,
          (∀ d d' : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
            (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) → f (d + d') = f d + f d') →
          (∀ (a : Λ) (d : Γ → Λ), (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
            f (a • d) = a * f d) →
          ∃ x : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) ∧
            ∀ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) → pair x d = f d) ∧
        (∀ f : (Γ → Λ) × (S → Λ) → Λ,
          (∀ x y : (Γ → Λ) × (S → Λ),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
            (IsLocallyConstant y.1 ∧ (∀ g h, y.1 (g * h) = y.1 g + y.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → y.1 g = 0) → f (x + y) = f x + f y) →
          (∀ (a : Λ) (x : (Γ → Λ) × (S → Λ)),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → f (a • x) = a * f x) →
          (∀ a : Λ, f (0, fun _ => a) = 0) →
          ∃ d : Γ → Λ, (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) ∧
            ∀ x : (Γ → Λ) × (S → Λ),
              (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) → pair x d = f x) ∧
        ∀ φ : KU ≃ₐ[F] KU, (∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) →
            φ x = x ^ Fintype.card Fq) →
          ∃ τ : S → S, ∃ η : S → Γ,
            (∀ s (b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU), (∃ c ∈ P s, (b : KU) = φ (c : KU)) ↔
              ∃ c ∈ P (τ s), (b : KU) = (η s : KU ≃ₐ[F] KU) (c : KU)) ∧
            ∀ (x : (Γ → Λ) × (S → Λ)) (d c' d' : Γ → Λ),
              (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + x.1 h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = 0) →
              (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + d h) →
              (∀ g g' : Γ, (g' : KU ≃ₐ[F] KU) = φ * g * φ⁻¹ → c' g = x.1 g' ∧ d' g = σ φ⁻¹ (d g')) →
              (IsLocallyConstant c' ∧ (∀ g h, c' (g * h) = c' g + c' h) ∧
                ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → c' g = 0) ∧
              (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + d' h) ∧
              pair (c', fun s => x.2 (τ s) - x.1 (η s)) d' =
                ((Fintype.card Fq : Λ) * σ φ⁻¹ 1) * pair x d := by
  sorry
