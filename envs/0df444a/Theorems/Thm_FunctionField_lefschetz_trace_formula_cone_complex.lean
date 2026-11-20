-- Prove2me | Theorems.Thm_FunctionField_lefschetz_trace_formula_cone_complex
-- name    : FunctionField.lefschetz_trace_formula_cone_complex
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:36:08.54714+00:00
-- url     : https://prove2.me/theorems/0c2164e8-a741-43e3-8561-6d803dff7727
-- title:
--   Grothendieck–Lefschetz trace formula mod $\ell^n$ for a lisse sheaf on an affine curve over $\mathbb F_q$, on the compactly supported cochain complex of $\pi_1$
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q=p^e$ elements ($p$ prime, $e\ge1$) and let $F$ be a function field over $\mathbb F_q$ (a finite separable extension of $\mathbb F_q(t)$) of characteristic $p$. Let $A\subset F$ be the integral closure of $\mathbb F_q[t]$, so that $U=\operatorname{Spec}A$ is the affine curve obtained from the complete curve $X$ of $F$ by removing the places over $t=\infty$, and let $R_\infty\subset F$ be the integral closure of the valuation ring of $\mathbb F_q(t)$ at infinity. Fix an algebraic closure $\overline F$ and let $K_U\subset\overline F$ be the compositum of all finite Galois extensions $L/F$ in $\overline F$ that are unramified over $A$: for every prime $\mathfrak P$ of the integral closure $A_L$ of $A$ in $L$, the only $g\in\mathrm{Gal}(L/F)$ with $g(b)\equiv b\pmod{\mathfrak P}$ for all $b\in A_L$ is $g=1$. Thus $\mathrm{Gal}(K_U/F)$ with its Krull topology is $\pi_1(U)$, and
--   $$\Gamma=\{g\in\mathrm{Gal}(K_U/F):\ g(x)=x\text{ for every }x\in K_U\text{ with }x^{q^k}=x\text{ for some }k\ge1\}$$
--   is the geometric fundamental group $\pi_1(\bar U)$. Let $\varphi\in\mathrm{Gal}(K_U/F)$ act on these constants by $x\mapsto x^q$ (such a $\varphi$ exists exactly when the constant field of $F$ is $\mathbb F_q$).
--
--   **Coefficients.** Let $M_f\subseteq K_U$ be a finite Galois extension of $F$ unramified over $A$ (in the same sense), $G$ a finite group and $\pi:\mathrm{Gal}(K_U/F)\to G$ a homomorphism whose kernel is $\mathrm{Gal}(K_U/M_f)$. Let $\ell\nmid q$ be a prime, $n\ge1$, and $M$ a free $\mathbb Z/\ell^n$-module of finite rank with a representation $\tau:G\to\mathrm{GL}(M)$. So $M$ with the action $\tau\circ\pi$ of $\pi_1(U)$ is a lisse sheaf of free $\mathbb Z/\ell^n$-modules on $U$, trivialized on the étale cover $\operatorname{Spec}A_{M_f}\to U$.
--
--   **Points.** Let $m,r\ge1$ with $m\,|G|\mid r$, let $\Omega$ be an algebraically closed field with $\mathrm{Fr}(z)=z^{q^m}$, let $C_r=\{x\in K_U:\ x^{q^r}=x\}\cong\mathbb F_{q^r}$ and fix a ring homomorphism $\iota:C_r\to\Omega$. Let $S$ be the finite set of ring homomorphisms $u:A\to\Omega$ that agree with $\iota$ on $\mathbb F_q$ and satisfy $\mathrm{Fr}\circ u=u$; these are the $\mathbb F_{q^m}$-rational points of $U$ (for the $\mathbb F_q$-structure on $\Omega$ given by $\iota$). For each $u\in S$ let $\mathrm{Fr}_u\in\mathrm{Gal}(K_U/F)$ be an arithmetic Frobenius element at $u$: some ring homomorphism $w$ from the integral closure $A_{K_U}$ of $A$ in $K_U$ to $\Omega$ extends $u$, agrees with $\iota$ on $C_r$, and satisfies $w(\mathrm{Fr}_u\,b)=\mathrm{Fr}(w(b))$ for all $b\in A_{K_U}$.
--
--   For a subgroup $H\le\Gamma$ write $Z^1(H,M)$ for the $\mathbb Z/\ell^n$-module of locally constant $1$-cocycles $c:H\to M$, $c(gh)=c(g)+\tau(\pi g)\,c(h)$. Then there are a finite set $B$ and nonzero primes $\mathfrak P_s$ ($s\in B$) of the integral closure $R_{\infty,U}$ of $R_\infty$ in $K_U$ forming a system of representatives of the nonzero primes of $R_{\infty,U}$ modulo $\Gamma$ (every one is $g(\mathfrak P_s)$ for some $s$ and $g\in\Gamma$, and $g(\mathfrak P_s)=\mathfrak P_{s'}$ with $g\in\Gamma$ forces $s=s'$; so $B$ is the set of points of $\bar X\setminus\bar U$), a map $t:B\to B$ and elements $h_s\in\Gamma$ with $\varphi(\mathfrak P_s)=h_s(\mathfrak P_{t(s)})$, such that the following holds. Let $I_s=\{g:\ g(b)\equiv b\pmod{\mathfrak P_s}\text{ for all }b\in R_{\infty,U}\}$ be the inertia group of $\mathfrak P_s$. Then
--   $$F_1(c,y)=\Big(g\mapsto\tau(\pi\varphi^{-1})\,c(\varphi g\varphi^{-1}),\ \ s\mapsto\tau(\pi\varphi^{-1})\big(\tau(\pi h_s)\,y_{t(s)}-c(h_s)\big)\Big)$$
--   is a $\mathbb Z/\ell^n$-linear endomorphism of $Z^1(\Gamma,M)\times M^B$,
--   $$F_2(x)_s(g)=\tau\big(\pi(\varphi^{-1}h_s)\big)\,x_{t(s)}\big(h_s^{-1}\varphi g\varphi^{-1}h_s\big)\qquad(g\in\Gamma\cap I_s)$$
--   is a $\mathbb Z/\ell^n$-linear endomorphism of $\prod_{s\in B}Z^1(\Gamma\cap I_s,M)$, and
--   $$\operatorname{Tr}\big(\tau(\pi\varphi^{-1})^m\mid M\big)-\operatorname{Tr}\big(F_1^m\mid Z^1(\Gamma,M)\times M^B\big)+\operatorname{Tr}\Big(F_2^m\ \Big|\ \prod_{s\in B}Z^1(\Gamma\cap I_s,M)\Big)=\sum_{u\in S}\operatorname{Tr}\big(\tau(\pi\,\mathrm{Fr}_u)^{-1}\mid M\big).$$
--
--   Role: $M$, $Z^1(\Gamma,M)\times M^B$ and $\prod_s Z^1(\Gamma\cap I_s,M)$ are the terms in degrees $0,1,2$ of the cone of the restriction map $C^\bullet(\Gamma,M)\to\prod_{s}C^\bullet(\Gamma\cap I_s,M)$ (truncated using that $\Gamma$ and $\Gamma\cap I_s$ have $\ell$-cohomological dimension $\le1$), a complex of continuous cochains computing $R\Gamma_c(\bar U,M)$, and $F_1,F_2$ are the action of the geometric Frobenius $\varphi^{-1}$ on it. The identity is the Grothendieck–Lefschetz trace formula
--   $$\sum_i(-1)^i\operatorname{Tr}\big(F^m\mid H^i_c(\bar U,M)\big)=\sum_{x\in U(\mathbb F_{q^m})}\operatorname{Tr}\big(\mathrm{Frob}_x\mid M_{\bar x}\big)$$
--   at the cochain level, for a lisse sheaf of free $\mathbb Z/\ell^n$-modules (with geometric Frobenius on both sides); applied for all $m$ it gives the rationality of $L(U,M,t)$ modulo $\ell^n$. No hypothesis on the Picard group is needed.
--
--   **Formalization Note**: $\overline F$ is `AlgebraicClosure F`; $A$ is `FunctionField.ringOfIntegers Fq F` and $R_\infty$ is `integralClosure (RatFunc.inftyValuation Fq).valuationSubring F`; integral closures in intermediate fields are `integralClosure _ L`. $\mathrm{Gal}(K_U/F)$ is `KU ≃ₐ[F] KU` with Mathlib's Krull topology. $K_U$, $\Gamma$, $M_f$, $C_r$ and $Z^1(\Gamma,M)$ (`Z1`) are variables with defining conditions `hKU`, `hΓ`, `hMf`, `hCr`, `hZ1`; in the conclusion the inertia groups $I_s$ and the modules $Z^1(\Gamma\cap I_s,M)$ (`Z2 s`) are universally quantified variables with defining conditions. Congruences mod a prime are written elementwise (`∃ c ∈ P, (c : L) = g b - b`), and $g(\mathfrak P)$ is described by `b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g c`. $G$ is `Gf`, the kernel condition on $\pi$ is `hπ` (and `hπo` records that the kernel is open). $\ell\nmid q$ is `¬ l ∣ Fintype.card Fq`. The point set is a `Finset` `S` with defining condition `hS`, where "agrees with $\iota$ on $\mathbb F_q$" is `u c = ιS x` whenever `x ∈ Cr` is the image of `c ∈ Fq`; the Frobenius elements form a function `Fu` constrained only on `S` by `hFu`. The boundary data $B,\mathfrak P_s,t,h_s$ and the maps $F_1,F_2$ are existential; $F_1,F_2$ are pinned down completely by the displayed formulas (stated for every `g'` equal to the conjugate), and the identity holds for every choice of boundary data (the statement asserts it for one choice). Traces are `LinearMap.trace` over `ZMod (l ^ n)`; the three modules are free of finite rank, so these are ordinary traces. The hypotheses are satisfiable for every $F$ with constant field $\mathbb F_q$: for example $F=\mathbb F_q(t)$, $M_f=F$, $G$ trivial and $M=\mathbb Z/\ell^n$, where the right side is the number of points of $\mathbb A^1(\mathbb F_{q^m})$, i.e. $q^m$, modulo $\ell^n$.
-- source:
--   A. Grothendieck, Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki, exposé 279 (1964/65); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Rapport sur la formule des traces »; J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §13

import Mathlib

set_option autoImplicit false

theorem FunctionField.lefschetz_trace_formula_cone_complex
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p e : ℕ) [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hlq : ¬ l ∣ Fintype.card Fq)
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
    (φ : KU ≃ₐ[F] KU)
    (hφ : ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → φ x = x ^ Fintype.card Fq)
    (Mf : IntermediateField F (AlgebraicClosure F))
    (hMf : FiniteDimensional F Mf ∧ IsGalois F Mf ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) Mf), P.IsPrime →
        ∀ g : Mf ≃ₐ[F] Mf,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) Mf, ∃ c ∈ P, (c : Mf) = g b - b) →
            g = 1)
    (hMfU : Mf ≤ KU)
    (Gf : Type) [Group Gf] [Fintype Gf] (π : (KU ≃ₐ[F] KU) →* Gf)
    (hπ : ∀ σ : KU ≃ₐ[F] KU, π σ = 1 ↔ ∀ x : KU, (x : AlgebraicClosure F) ∈ Mf → σ x = x)
    (hπo : IsOpen (π.ker : Set (KU ≃ₐ[F] KU)))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Module.Free (ZMod (l ^ n)) M]
    [Module.Finite (ZMod (l ^ n)) M] (τ : Representation (ZMod (l ^ n)) Gf M)
    (Z1 : Submodule (ZMod (l ^ n)) (Γ → M))
    (hZ1 : ∀ c : Γ → M, c ∈ Z1 ↔ IsLocallyConstant c ∧ ∀ g h : Γ, c (g * h) = c g + τ (π g) (c h))
    (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : 0 < r) (hmr : m * Fintype.card Gf ∣ r)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ (Fintype.card Fq ^ m))
    (Cr : Subfield KU) (hCr : ∀ x : KU, x ∈ Cr ↔ x ^ (Fintype.card Fq ^ r) = x) (ιS : Cr →+* Ω)
    (S : Finset (FunctionField.ringOfIntegers Fq F →+* Ω))
    (hS : ∀ u, u ∈ S ↔ (∀ (c : Fq) (x : Cr), (x : KU) = algebraMap F KU (algebraMap Fq F c) →
        u (algebraMap Fq (FunctionField.ringOfIntegers Fq F) c) = ιS x) ∧ Fr.comp u = u)
    (Fu : (FunctionField.ringOfIntegers Fq F →+* Ω) → (KU ≃ₐ[F] KU))
    (hFu : ∀ u ∈ S, ∃ w : integralClosure (FunctionField.ringOfIntegers Fq F) KU →+* Ω,
      (∀ a : FunctionField.ringOfIntegers Fq F, w (algebraMap _ _ a) = u a) ∧
      (∀ b b' : integralClosure (FunctionField.ringOfIntegers Fq F) KU,
        (b' : KU) = Fu u (b : KU) → w b' = Fr (w b)) ∧
      ∀ (x : Cr) (b : integralClosure (FunctionField.ringOfIntegers Fq F) KU), (b : KU) = x → w b = ιS x) :
    ∃ (B : Type) (P : B → Ideal (integralClosure
        (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU)),
      Finite B ∧ (∀ s, (P s).IsPrime ∧ P s ≠ ⊥) ∧
      (∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
        Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
          ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
            b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) ∧
      (∀ s s', ∀ g ∈ Γ,
        (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
          b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s') ∧
      ∃ (t : B → B) (h : B → Γ),
        (∀ s (b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
          (∃ c ∈ P s, (b : KU) = φ (c : KU)) ↔
            ∃ c ∈ P (t s), (b : KU) = (h s : KU ≃ₐ[F] KU) (c : KU)) ∧
        ∀ I : B → Subgroup (KU ≃ₐ[F] KU),
          (∀ s (g : KU ≃ₐ[F] KU), g ∈ I s ↔
            ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
              ∃ c ∈ P s, (c : KU) = g (b : KU) - b) →
        ∀ Z2 : (s : B) → Submodule (ZMod (l ^ n)) (↥(Γ ⊓ I s) → M),
          (∀ s (c : ↥(Γ ⊓ I s) → M), c ∈ Z2 s ↔
            IsLocallyConstant c ∧ ∀ g h : ↥(Γ ⊓ I s), c (g * h) = c g + τ (π g) (c h)) →
        ∃ (F1 : (↥Z1 × (B → M)) →ₗ[ZMod (l ^ n)] (↥Z1 × (B → M)))
          (F2 : ((s : B) → ↥(Z2 s)) →ₗ[ZMod (l ^ n)] ((s : B) → ↥(Z2 s))),
          (∀ (c : ↥Z1) (y : B → M) (g g' : Γ), (g' : KU ≃ₐ[F] KU) = φ * g * φ⁻¹ →
            ((F1 (c, y)).1 : Γ → M) g = τ (π φ⁻¹) ((c : Γ → M) g')) ∧
          (∀ (c : ↥Z1) (y : B → M) (s : B),
            (F1 (c, y)).2 s = τ (π φ⁻¹) (τ (π (h s)) (y (t s)) - (c : Γ → M) (h s))) ∧
          (∀ (x : (s : B) → ↥(Z2 s)) (s : B) (g : ↥(Γ ⊓ I s)) (g' : ↥(Γ ⊓ I (t s))),
            (g' : KU ≃ₐ[F] KU) = (h s : KU ≃ₐ[F] KU)⁻¹ * φ * g * φ⁻¹ * h s →
            ((F2 x s : ↥(Z2 s)) : ↥(Γ ⊓ I s) → M) g =
              τ (π (φ⁻¹ * h s)) (((x (t s) : ↥(Z2 (t s))) : ↥(Γ ⊓ I (t s)) → M) g')) ∧
          LinearMap.trace (ZMod (l ^ n)) M (τ (π φ⁻¹) ^ m) -
              LinearMap.trace (ZMod (l ^ n)) (↥Z1 × (B → M)) (F1 ^ m) +
              LinearMap.trace (ZMod (l ^ n)) ((s : B) → ↥(Z2 s)) (F2 ^ m) =
            ∑ u ∈ S, LinearMap.trace (ZMod (l ^ n)) M (τ (π (Fu u))⁻¹) := by sorry
