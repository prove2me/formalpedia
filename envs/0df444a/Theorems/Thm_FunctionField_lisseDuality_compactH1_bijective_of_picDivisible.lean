-- Prove2me | Theorems.Thm_FunctionField_lisseDuality_compactH1_bijective_of_picDivisible
-- name    : FunctionField.lisseDuality_compactH1_bijective_of_picDivisible
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:26:54.63368+00:00
-- url     : https://prove2.me/theorems/99699c42-3222-4ffe-9526-0268b6dedfe6
-- title:
--   Poincaré duality with lisse coefficients on an affine curve over $\overline{\mathbb F}_q$: $H^1_c(\bar U,M)\to\operatorname{Hom}(H^1(\bar U,M^\vee(1)),\Lambda)$ is bijective
-- statement:
--   Let $\mathbb F_q$ be a finite field of characteristic $p$, $q=p^e$ with $e\ge1$, and let $F$ be a function field over $\mathbb F_q$ (a finite separable extension of $\mathbb F_q(t)$) whose constant field is exactly $\mathbb F_q$. Let $A\subset F$ be the integral closure of $\mathbb F_q[t]$, so that $U=\operatorname{Spec}A$ is the smooth affine curve obtained from the complete curve $X$ of $F$ by removing the places over $t=\infty$, and let $R_\infty\subset F$ be the integral closure of the valuation ring of $\mathbb F_q(t)$ at infinity. Fix an algebraic closure $\overline F$ and let $K_U\subset\overline F$ be the compositum of all finite Galois extensions $L/F$ in $\overline F$ that are unramified over $A$: for every prime $\mathfrak P$ of the integral closure $A_L$ of $A$ in $L$, the only $g\in\mathrm{Gal}(L/F)$ with $g(b)\equiv b\pmod{\mathfrak P}$ for all $b\in A_L$ is $g=1$. Thus $\mathrm{Gal}(K_U/F)$ with its Krull topology is $\pi_1(U)$, and
--   $$\Gamma=\{g\in\mathrm{Gal}(K_U/F):\ g(x)=x\text{ for every }x\in K_U\text{ with }x^{q^k}=x\text{ for some }k\ge1\}=\mathrm{Gal}(K_U/F\overline{\mathbb F}_q)$$
--   is the geometric fundamental group $\pi_1(\bar U)$.
--
--   The nonzero primes of the integral closure $R_{\infty,U}$ of $R_\infty$ in $K_U$ are the places of $K_U$ over the points at infinity. Let $S$ be a finite nonempty set and $\mathfrak P_s$ ($s\in S$) nonzero primes of $R_{\infty,U}$ forming a system of representatives of these primes modulo $\Gamma$ (every one is $g(\mathfrak P_s)$ for some $s$ and $g\in\Gamma$, and $g(\mathfrak P_s)=\mathfrak P_{s'}$ with $g\in\Gamma$ forces $s=s'$); so $S$ is the set of points of $\bar X\setminus\bar U$. Let $I_s=\{g:\ g(b)\equiv b\pmod{\mathfrak P_s}\text{ for all }b\in R_{\infty,U}\}$ be the inertia group of $\mathfrak P_s$.
--
--   Let $\ell\ne p$ be a prime, $n\ge1$, and $\Lambda$ a finite commutative ring with $\ell^n\Lambda=0$ which is self-injective ($\Lambda$ is an injective $\Lambda$-module) and whose duals separate points (for every finite $\Lambda$-module $N$ and $0\ne m\in N$ some $\varphi\in\operatorname{Hom}_\Lambda(N,\Lambda)$ has $\varphi(m)\ne0$), for example $\Lambda=\mathbb Z/\ell^n$. Let $\sigma$ be a continuous action of $\mathrm{Gal}(K_U/F)$ on $\Lambda$ by $\Lambda$-linear maps that is trivial on $\Gamma$ (the twist $\Lambda(1)$). Assume the two divisor-class facts that are the input of the computation of $H^2$:
--
--   * (Pic of $\bar U$ is $\ell$-divisible) for every finite extension $M\subseteq K_U$ of $F$ and every divisor $D$ of the affine curve $U_M=\operatorname{Spec}A_M$ there are $m\ge1$ and $a\ne0$ in $M_m=M\,\mathbb F_{p^m}$ with $D+\operatorname{div}(a)\equiv0\pmod\ell$ on $U_{M_m}$ (that is, $\ell\mid D(v)+v_w(a)$ for every prime $w$ of $A_{M_m}$ over the prime $v$ of $A_M$);
--   * ($\operatorname{Pic}^0(\bar X)$ is $\ell$-divisible) for every finite $M\subseteq K_U$ all of whose places at infinity have the same residue field size, and every divisor $D$ supported at infinity of total multiplicity $0$, there are $m\ge1$ and $a\ne0$ in $M_m$ with $\operatorname{div}(a)\equiv0\pmod{\ell^n}$ on $U_{M_m}$ and $D+\operatorname{div}(a)\equiv0\pmod{\ell^n}$ at the places at infinity of $M_m$.
--
--   Let $E\subseteq K_U$ be a finite Galois extension of $F$ unramified over $A$ (in the sense above), with corresponding finite étale Galois cover $V\to U$, and let $\pi:\mathrm{Gal}(K_U/F)\to G_f$ be a homomorphism to a finite group whose kernel is $\mathrm{Gal}(K_U/E)$. Assume that $\Gamma\cap\ker\pi=\pi_1(\bar V)$ has only finitely many continuous homomorphisms to $\mathbb Z/\ell$ (that is, $H^1(\bar V,\mathbb Z/\ell)$ is finite). Let $M$ be a finite $\Lambda$-module with a $\Lambda$-linear action $\tau$ of $G_f$. Through $\pi$, $M$ is a lisse sheaf on $U$ trivialized on $V$; its twisted dual $M^\vee(1)=\operatorname{Hom}_\Lambda(M,\Lambda)$ carries the action $g\cdot\varphi=\sigma(g)\circ\varphi\circ\tau(\pi(g))^{-1}$.
--
--   In cochain form, $H^1(\bar U,M^\vee(1))$ consists of the locally constant $d:\Gamma\to M^\vee(1)$ with $d(gh)=d(g)+g\cdot d(h)$, modulo the coboundaries $g\mapsto g\cdot\varphi-\varphi$, and $H^1_c(\bar U,M)$ is the first cohomology of the cone of restriction to the boundary: pairs $(c,m)$ of a locally constant $c:\Gamma\to M$ with $c(gh)=c(g)+\tau(\pi g)\,c(h)$ and $m\in M^S$ with $c(g)=\tau(\pi g)\,m_s-m_s$ for $g\in\Gamma\cap I_s$, modulo the pairs $\big(g\mapsto\tau(\pi g)\,m-m,\ (m)_{s\in S}\big)$. Then there are $t_s\in\Gamma\cap I_s$ such that:
--
--   1. for every such cocycle $c$ and every cocycle $d$, the $2$-cocycle $(g,h)\mapsto (g\cdot d(h))(c(g))$ is a coboundary: $(g\cdot d(h))(c(g))=\sigma(g)\,u(h)-u(gh)+u(g)$ for some locally constant $u:\Gamma\to\Lambda$;
--   2. there is a pairing on cochains with
--   $$\langle (c,m),d\rangle=\sum_{s\in S}\big(d(t_s)(m_s)-u(t_s)\big)$$
--   for every relative cocycle $(c,m)$, every cocycle $d$ and every primitive $u$ of $c\cup d$ as in item 1, and the induced duality map $H^1_c(\bar U,M)\to\operatorname{Hom}_\Lambda(H^1(\bar U,M^\vee(1)),\Lambda)$ is bijective: if $\langle x,d\rangle=0$ for every cocycle $d$, then $x$ is a relative coboundary $\big(g\mapsto\tau(\pi g)\,m-m,\ (m)_s\big)$; and every function $f$ on cocycles $d$ that is additive and $\Lambda$-homogeneous on cocycles and vanishes on the coboundaries is $f=\langle x,\cdot\rangle$ on cocycles for some relative cocycle $x$.
--
--   Role: Poincaré duality for the degree-$1$ cohomology of the affine curve $\bar U$ over $\overline{\mathbb F}_q$ with coefficients in an arbitrary lisse sheaf of finite $\Lambda$-modules (one trivialized on a finite étale Galois cover), $H^1_c(\bar U,M)\cong\operatorname{Hom}_\Lambda(H^1(\bar U,M^\vee(1)),\Lambda)$, written in continuous cochains of the Galois group of the maximal extension unramified over $U$, with the trace $H^2_c(\bar U,\Lambda(1))\cong\Lambda$ made explicit by the elements $t_s$. It extends the constant-coefficient case (FunctionField.cupPairing_compactH1_geomH1_isPerfect_of_picDivisible). The divisibility hypotheses and the finiteness of $H^1(\bar V,\mathbb Z/\ell)$ hold for every curve when $\ell\ne p$ ($\operatorname{Pic}^0$ is a divisible group and $H^1(\bar V,\mathbb Z/\ell)\cong(\mathbb Z/\ell)^{2g_V+r_V-1}$); they are assumed only because these facts are not available in Mathlib.
--
--   **Formalization Note**: $\overline F$ is `AlgebraicClosure F`; $A$ is `FunctionField.ringOfIntegers Fq F` and $R_\infty$ is `integralClosure (RatFunc.inftyValuation Fq).valuationSubring F`; integral closures in intermediate fields are `integralClosure _ M`. The constant field condition is `algebraicClosure Fq F = ⊥`. $K_U$, the constant field levels $F\mathbb F_{p^m}$ (`CL m`, the adjunction of the roots of $X^{p^m}-X$), $\Gamma$ and the inertia groups $I_s$ are variables with defining equations `hKU`, `hCL`, `hΓ`, `hI`; congruences mod a prime are written elementwise (`∃ c ∈ P, (c : L) = g b - b`), and $g(\mathfrak P)$ is described by `b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g c`. $\mathrm{Gal}(K_U/F)$ is `KU ≃ₐ[F] KU` with Mathlib's Krull topology; continuity of cochains on $\Gamma$ is `IsLocallyConstant`; $\sigma$ is a `Representation Λ (KU ≃ₐ[F] KU) Λ` with open kernel; $\ell^n\Lambda=0$ is `((l ^ n : ℕ) : Λ) = 0` and $\ell\ne p$ is `(l : F) ≠ 0`; self-injectivity is `Module.Injective Λ Λ` and the separation property is `hsep`. The extension $E$ is an intermediate field of `AlgebraicClosure F` with the same unramifiedness condition as in `hKU` (`hE`) and `hEU : E ≤ KU`; `hπ` says `π g = 1` iff `g` fixes every element of $K_U$ lying in $E$. The finiteness hypothesis `hfin` is about `Γ.subgroupOf π.ker` (the group $\Gamma\cap\ker\pi$, as a subgroup of `π.ker`, with the subspace topology). The action on $M$ is `τ (π g)` and the action on $M^\vee(1)$ is `Representation.linHom (τ.comp π) σ`. Cochains are plain functions: a relative cocycle is `x : (Γ → M) × (S → M)`, a cocycle for $M^\vee(1)$ is `d : Γ → (M →ₗ[Λ] Λ)`, the pairing is a function `pair` on representatives determined by the formula of item 2, and bijectivity is stated elementwise (injectivity on classes and representability of functionals on $H^1$). Divisors are finitely supported functions on `IsDedekindDomain.HeightOneSpectrum` of the relevant integral closure, $v_w(a)$ is `WithZero.log (w.valuation _ a)` (up to sign, which does not matter for the divisibility conditions), and "$w$ lies over $v$" is written elementwise in $\overline F$; the Dedekind and fraction-ring instances of these integral closures are taken as instance arguments inside the hypotheses. The hypotheses are satisfiable for every $F$ as above (they are theorems for every curve and every $\ell\ne p$), for example for $F=\mathbb F_q(t)$, $E=F$, $G_f$ trivial and $\Lambda=\mathbb Z/\ell^n$: then $U=\mathbb A^1$, $S$ is a single point, $\operatorname{Pic}(\bar U)=\operatorname{Pic}^0(\bar X)=0$ and $H^1(\mathbb A^1_{\overline{\mathbb F}_q},\mathbb Z/\ell)=0$.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib

set_option autoImplicit false

theorem FunctionField.lisseDuality_compactH1_bijective_of_picDivisible
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p e : ℕ) [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (hk : algebraicClosure Fq F = ⊥)
    (l : ℕ) [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ) (hn : n ≠ 0)
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
    (hPicU : ∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) M)]
        [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) M) M]
        (D : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M) → ℤ),
        (Function.support D).Finite →
        ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
          ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))]
            [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
              ↥(M ⊔ CL m)]
            (w : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
              ↥(M ⊔ CL m)))
            (v : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M)),
            (∀ x : integralClosure (FunctionField.ringOfIntegers Fq F) M, x ∈ v.asIdeal ↔
              ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                  AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
            (l : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a))
    (hPic : ∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)]
        [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) M]
        (r : ℕ),
        (∀ w : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M),
          Nat.card (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M ⧸
            w.asIdeal) = r) →
        ∀ D : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) → ℤ,
          (Function.support D).Finite → ∑ᶠ w, D w = 0 →
          ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
            (∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (y : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))),
              ((l ^ n : ℕ) : ℤ) ∣ WithZero.log (y.valuation ↥(M ⊔ CL m) a)) ∧
            ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (w : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m)))
              (v : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)),
              (∀ x : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M,
                x ∈ v.asIdeal ↔ ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                    AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
              ((l ^ n : ℕ) : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a))
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
    (E : IntermediateField F (AlgebraicClosure F))
    (hE : FiniteDimensional F E ∧ IsGalois F E ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) E), P.IsPrime →
        ∀ g : E ≃ₐ[F] E,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) E, ∃ c ∈ P, (c : E) = g b - b) →
            g = 1)
    (hEU : E ≤ KU)
    (Gf : Type) [Group Gf] [Finite Gf] (π : (KU ≃ₐ[F] KU) →* Gf)
    (hπ : ∀ g : KU ≃ₐ[F] KU, π g = 1 ↔ ∀ x : KU, (x : AlgebraicClosure F) ∈ E → g x = x)
    (hfin : {y : ↥(Γ.subgroupOf π.ker) → ZMod l |
      IsLocallyConstant y ∧ ∀ a b, y (a * b) = y a + y b}.Finite)
    (Λ : Type) [CommRing Λ] [Finite Λ] [Module.Injective Λ Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (hsep : ∀ (N : Type) [AddCommGroup N] [Module Λ N] [Finite N] (m : N), m ≠ 0 →
      ∃ φ : N →ₗ[Λ] Λ, φ m ≠ 0)
    (σ : Representation Λ (KU ≃ₐ[F] KU) Λ) (hσ : IsOpen (σ.ker : Set (KU ≃ₐ[F] KU)))
    (htriv : ∀ g ∈ Γ, ∀ x : Λ, σ g x = x)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M) :
    ∃ t : S → Γ, (∀ s, (t s : KU ≃ₐ[F] KU) ∈ I s) ∧
      (∀ (c : Γ → M) (d : Γ → (M →ₗ[Λ] Λ)),
        (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + τ (π g) (c h)) →
        (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
        ∃ u : Γ → Λ, IsLocallyConstant u ∧
          ∀ g h : Γ, (Representation.linHom (τ.comp π) σ) g (d h) (c g) = σ g (u h) - u (g * h) + u g) ∧
      ∃ pair : (Γ → M) × (S → M) → (Γ → (M →ₗ[Λ] Λ)) → Λ,
        (∀ (x : (Γ → M) × (S → M)) (d : Γ → (M →ₗ[Λ] Λ)) (u : Γ → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s) →
          (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
          (IsLocallyConstant u ∧
            ∀ g h : Γ, (Representation.linHom (τ.comp π) σ) g (d h) (x.1 g) = σ g (u h) - u (g * h) + u g) →
          pair x d = ∑ s, (d (t s) (x.2 s) - u (t s))) ∧
        (∀ x : (Γ → M) × (S → M),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s) →
          (∀ d : Γ → (M →ₗ[Λ] Λ),
            (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
              pair x d = 0) →
          ∃ m : M, (∀ g : Γ, x.1 g = τ (π g) m - m) ∧ ∀ s, x.2 s = m) ∧
        ∀ f : (Γ → (M →ₗ[Λ] Λ)) → Λ,
          (∀ d d' : Γ → (M →ₗ[Λ] Λ),
            (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
            (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + (Representation.linHom (τ.comp π) σ) g (d' h)) →
              f (d + d') = f d + f d') →
          (∀ (a : Λ) (d : Γ → (M →ₗ[Λ] Λ)),
            (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
              f (a • d) = a * f d) →
          (∀ φ : M →ₗ[Λ] Λ, f (fun g => (Representation.linHom (τ.comp π) σ) g φ - φ) = 0) →
          ∃ x : (Γ → M) × (S → M),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s) ∧
            ∀ d : Γ → (M →ₗ[Λ] Λ),
              (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
                pair x d = f d := by
  sorry
