-- Prove2me | Theorems.Thm_FunctionField_riemannHurwitz_differentIdeal
-- name    : FunctionField.riemannHurwitz_differentIdeal
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:32:56.86719+00:00
-- url     : https://prove2.me/theorems/40edcc85-bf39-435a-8178-7bceabe5b138
-- title:
--   Riemann–Hurwitz formula with the different, wild ramification allowed: $2g_L - 2\ell_L(0) = [L:K]\,(2g_K - 2\ell_K(0)) + \deg \mathrm{Diff}(L/K)$ for function fields over a finite field
-- statement:
--   Let $\mathbb{F}_q$ be a finite field and let $K$ and $L$ be algebraic function fields over $\mathbb{F}_q$, presented as finite separable extensions of the rational function field $\mathbb{F}_q(x)$, with $L$ a compatible extension of $K$ (so $L/K$ is finite and separable). For such a field $F$ let $R_F$ be the integral closure of $\mathbb{F}_q[x]$ in $F$ (its prime ideals are the places of $F$ not over $x = \infty$) and let $R_F^\infty$ be the integral closure in $F$ of the valuation ring $\mathcal{O}_\infty = \{ f/g : \deg f \le \deg g \}$ of $\mathbb{F}_q(x)$ at infinity (its prime ideals are the places over $x = \infty$). Both are Dedekind domains, and together their height-one primes are all the places of $F$.
--
--   **Riemann–Roch data.** Let $D_\infty$ be the pole divisor of $x$, so $\deg D_\infty = [F : \mathbb{F}_q(x)]$ and $\mathcal{L}(n D_\infty) = \{ f \in R_F : f x^{-n} \in R_F^\infty \}$. Put $\ell_F(0) = \dim_{\mathbb{F}_q} \mathcal{L}(0) = \dim_{\mathbb{F}_q} (R_F \cap R_F^\infty)$, the degree over $\mathbb{F}_q$ of the full constant field $k_F$ of $F$, and let $g_F$ be the genus measured over $\mathbb{F}_q$: by Riemann's theorem $\dim_{\mathbb{F}_q} \mathcal{L}(n D_\infty) = n\,[F : \mathbb{F}_q(x)] + \ell_F(0) - g_F$ for all large $n$, and this determines $g_F$. One has $g_F = [k_F : \mathbb{F}_q]\, g(F/k_F)$, so $2 g_F - 2 \ell_F(0) = [k_F : \mathbb{F}_q]\,(2 g(F/k_F) - 2)$ is the $\mathbb{F}_q$-degree of a canonical divisor of $F$.
--
--   **The different.** Let $\mathfrak{D}_{\mathrm{fin}} \subseteq R_L$ be the different ideal of $R_L / R_K$ and $\mathfrak{D}_\infty \subseteq R_L^\infty$ the different ideal of $R_L^\infty / R_K^\infty$ (the inverse of the trace dual). Together they form the different divisor $\mathrm{Diff}(L/K) = \sum_Q d(Q|P)\, Q$ of $L/K$, and its degree over $\mathbb{F}_q$ is given by $q^{\deg \mathrm{Diff}(L/K)} = \# (R_L / \mathfrak{D}_{\mathrm{fin}}) \cdot \# (R_L^\infty / \mathfrak{D}_\infty)$.
--
--   **Statement (Hurwitz genus formula).**
--
--   $$2 g_L - 2 \ell_L(0) = [L:K]\,\bigl(2 g_K - 2 \ell_K(0)\bigr) + \deg \mathrm{Diff}(L/K).$$
--
--   No tameness is assumed: by Dedekind's different theorem $d(Q|P) \ge e(Q|P) - 1$, with equality exactly when $Q|P$ is tame, and wild ramification contributes $d(Q|P) \ge e(Q|P)$. When $\mathbb{F}_q$ is the full constant field of $K$ and of $L$ this is the familiar $2g_L - 2 = [L:K](2g_K - 2) + \deg \mathrm{Diff}(L/K)$ (Stichtenoth, Theorem 3.4.13). No completions are used: the different is Mathlib's `differentIdeal` on the two affine charts.
--
--   **Formalization Note**: `Fq`, `K`, `L` are fields in `Type`, with `[Fintype Fq]` and `[DecidableEq (RatFunc Fq)]` (needed by `RatFunc.inftyValuation`). Each of `K`, `L` carries Mathlib's function field package: `Algebra Fq _`, `Algebra (Polynomial Fq) _`, `Algebra (RatFunc Fq) _` with the scalar towers `IsScalarTower (Polynomial Fq) (RatFunc Fq) _` and `IsScalarTower Fq (Polynomial Fq) _`, `[FunctionField Fq _]` (finite over `RatFunc Fq`) and `[Algebra.IsSeparable (RatFunc Fq) _]`; `[Algebra K L]` is compatible with all three base rings (scalar towers `Fq`, `Polynomial Fq`, `RatFunc Fq` over `K` to `L`). $R_F$ is `FunctionField.ringOfIntegers Fq F` and $R_F^\infty$ is `integralClosure (RatFunc.inftyValuation Fq).valuationSubring F`. The ring maps $R_K \to R_L$ and $R_K^\infty \to R_L^\infty$ are instance arguments `Algebra _ _` pinned by `IsScalarTower _ _ L` (so each is the restriction of $K \to L$; there is exactly one such instance). The remaining instance arguments are true facts that `differentIdeal` needs and that Mathlib does not infer here: `Module.IsTorsionFree` for both chart extensions and `IsDedekindDomain` for both integral closures of $\mathcal{O}_\infty$. The numbers are natural-number variables pinned by hypotheses: `eK` by `heK` ($\#(R_K \cap R_K^\infty) = q^{e_K}$, so $e_K = \ell_K(0)$; `Nat.card` of the subtype of `K`), `gK` by `hgK` (for all large `n`, $\#\mathcal{L}(n D_\infty) \cdot q^{g_K} = q^{n [K : \mathbb{F}_q(x)] + e_K}$, with $x$ = `algebraMap (Polynomial Fq) K Polynomial.X` and $[K : \mathbb{F}_q(x)]$ = `Module.finrank (RatFunc Fq) K`), likewise `eL`, `gL`, and `d` by `hd` (the product of the cardinalities of the two quotients by the different ideals is $q^d$, so $d = \deg \mathrm{Diff}(L/K)$). The conclusion is `2 * (gL : ℤ) - 2 * eL = (Module.finrank K L : ℤ) * (2 * (gK : ℤ) - 2 * eK) + d`. The statement is not vacuous: for every such pair $K \subseteq L$ the numbers $e$, $g$, $d$ exist (finiteness of $\mathcal{L}(D)$, Riemann's theorem, and $\mathfrak{D} \neq 0$ for separable $L/K$), for example $K = \mathbb{F}_q(x)$ and $L$ the Artin–Schreier extension $y^q - y = x$, which is wildly ramified at $\infty$.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Theorem 3.4.13 (Hurwitz Genus Formula) and Theorem 3.5.1 (Dedekind's Different Theorem)

import Mathlib

set_option autoImplicit false

theorem FunctionField.riemannHurwitz_differentIdeal
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (K : Type) [Field K] [Algebra Fq K] [Algebra (Polynomial Fq) K] [Algebra (RatFunc Fq) K]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) K] [IsScalarTower Fq (Polynomial Fq) K] [FunctionField Fq K]
    [Algebra.IsSeparable (RatFunc Fq) K]
    (L : Type) [Field L] [Algebra Fq L] [Algebra (Polynomial Fq) L] [Algebra (RatFunc Fq) L]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) L] [IsScalarTower Fq (Polynomial Fq) L] [FunctionField Fq L]
    [Algebra.IsSeparable (RatFunc Fq) L]
    [Algebra K L] [IsScalarTower Fq K L] [IsScalarTower (Polynomial Fq) K L] [IsScalarTower (RatFunc Fq) K L]
    [Algebra (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)]
    [IsScalarTower (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L) L]
    [Module.IsTorsionFree (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)]
    [Algebra (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    [IsScalarTower (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) L]
    [IsDedekindDomain (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)]
    [IsDedekindDomain (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    [Module.IsTorsionFree (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)]
    (gK gL eK eL d : ℕ)
    (heK : Nat.card {f : K // f ∈ FunctionField.ringOfIntegers Fq K ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring K} = Fintype.card Fq ^ eK)
    (heL : Nat.card {f : L // f ∈ FunctionField.ringOfIntegers Fq L ∧
      f ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring L} = Fintype.card Fq ^ eL)
    (hgK : ∃ N : ℕ, ∀ n ≥ N, Nat.card {f : K // f ∈ FunctionField.ringOfIntegers Fq K ∧
      f * (algebraMap (Polynomial Fq) K Polynomial.X)⁻¹ ^ n ∈
        integralClosure (RatFunc.inftyValuation Fq).valuationSubring K} *
        Fintype.card Fq ^ gK = Fintype.card Fq ^ (n * Module.finrank (RatFunc Fq) K + eK))
    (hgL : ∃ N : ℕ, ∀ n ≥ N, Nat.card {f : L // f ∈ FunctionField.ringOfIntegers Fq L ∧
      f * (algebraMap (Polynomial Fq) L Polynomial.X)⁻¹ ^ n ∈
        integralClosure (RatFunc.inftyValuation Fq).valuationSubring L} *
        Fintype.card Fq ^ gL = Fintype.card Fq ^ (n * Module.finrank (RatFunc Fq) L + eL))
    (hd : Nat.card (FunctionField.ringOfIntegers Fq L ⧸
        differentIdeal (FunctionField.ringOfIntegers Fq K) (FunctionField.ringOfIntegers Fq L)) *
      Nat.card (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L ⧸
        differentIdeal (integralClosure (RatFunc.inftyValuation Fq).valuationSubring K)
          (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)) = Fintype.card Fq ^ d) :
    2 * (gL : ℤ) - 2 * eL = (Module.finrank K L : ℤ) * (2 * (gK : ℤ) - 2 * eK) + d := by
  sorry
