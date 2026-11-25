-- Prove2me | Theorems.Thm_FunctionField_geomPic_affine_divisible_and_geomPic0_divisible
-- name    : FunctionField.geomPic_affine_divisible_and_geomPic0_divisible
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:48:33.53746+00:00
-- url     : https://prove2.me/theorems/7fe70d9b-23b0-548b-9067-4e3b92ffc13b
-- title:
--   For an affine curve $U$ over $\mathbb F_q$ and a prime $\ell\nmid q$: $\operatorname{Pic}(\bar U)$ is $\ell$-divisible and $\operatorname{Pic}^0(\bar X)$ is $\ell^n$-divisible
-- statement:
--   Let $\mathbb F_q$ be a finite field of characteristic $p$ and let $F$ be a function field over $\mathbb F_q$ (a finite separable extension of $\mathbb F_q(t)$). Let $A\subset F$ be the integral closure of $\mathbb F_q[t]$, so that $U=\operatorname{Spec}A$ is the smooth affine curve obtained from the complete curve $X$ of $F$ by removing the places over $t=\infty$, and let $R_\infty\subset F$ be the integral closure of the valuation ring of $\mathbb F_q(t)$ at infinity (its maximal ideals are the points of $X$ over $\infty$). Fix an algebraic closure $\overline F$, let $F_m=F\,\mathbb F_{p^m}\subseteq\overline F$ be generated over $F$ by the roots of $T^{p^m}-T$, and let $K_U\subset\overline F$ be the compositum of all finite Galois extensions $L/F$ in $\overline F$ that are unramified over $A$: for every prime $\mathfrak P$ of the integral closure $A_L$ of $A$ in $L$, the only $g\in\mathrm{Gal}(L/F)$ with $g(b)\equiv b\pmod{\mathfrak P}$ for all $b\in A_L$ is $g=1$. For a field $M$ with $F\subseteq M\subseteq\overline F$ write $A_M$, $R_{\infty,M}$ for the integral closures of $A$, $R_\infty$ in $M$ and $M_m=M\,F_m$; for a prime $w$ of $A_{M_m}$ (or of $R_{\infty,M_m}$) and $a\in M_m^\times$, $v_w(a)$ is the $w$-adic valuation of $a$.
--
--   Let $\ell\ne p$ be a prime and $n\ge0$. Then for every finite extension $M/F$ with $M\subseteq K_U$:
--
--   1. ($\operatorname{Pic}(\bar U)$ is $\ell$-divisible.) For every divisor $D$ of the affine curve $U_M=\operatorname{Spec}A_M$ (a finitely supported integer function on the nonzero primes of $A_M$) there are $m\ge1$ and $a\ne0$ in $M_m$ with $D+\operatorname{div}(a)\equiv0\pmod\ell$ on $U_{M_m}$, that is, $\ell\mid D(v)+v_w(a)$ for every prime $w$ of $A_{M_m}$ and the prime $v=w\cap A_M$ below it.
--
--   2. ($\operatorname{Pic}^0(\bar X)$ is $\ell^n$-divisible.) If all points at infinity of $M$ (the nonzero primes of $R_{\infty,M}$) have residue fields of the same size, then for every divisor $D$ supported at infinity, i.e. a finitely supported integer function on the nonzero primes of $R_{\infty,M}$, with $\sum_w D(w)=0$, there are $m\ge1$ and $a\ne0$ in $M_m$ with $\ell^n\mid v_y(a)$ for every prime $y$ of $A_{M_m}$ and $\ell^n\mid D(v)+v_w(a)$ for every prime $w$ of $R_{\infty,M_m}$ and the prime $v=w\cap R_{\infty,M}$ below it.
--
--   Role: these are the two divisor-class facts that compute $H^2$ in the étale cohomology of the curve over $\overline{\mathbb F}_q$: $\operatorname{Pic}(\bar U)/\ell=0$ and the $\ell^n$-divisibility of $\operatorname{Pic}^0(\bar X)=J(\overline{\mathbb F}_q)$ (the Jacobian is a divisible group; with all points at infinity of the same degree a degree-$0$ divisor at infinity becomes $\ell^n$ times a divisor plus a principal divisor over a large enough constant field). Statements 1 and 2 are word for word the hypotheses `hPicU` and `hPic` of the Poincaré duality theorem `FunctionField.cupPairing_compactH1_geomH1_isPerfect_of_picDivisible`, so together with it they give Poincaré duality on affine curves over $\overline{\mathbb F}_q$ without hypotheses.
--
--   **Formalization Note**: $\overline F$ is `AlgebraicClosure F`; $A$ is `FunctionField.ringOfIntegers Fq F` and $R_\infty$ is `integralClosure (RatFunc.inftyValuation Fq).valuationSubring F`; integral closures in intermediate fields are `integralClosure _ M`. $K_U$ and the constant field levels $F_m$ (`CL m`, the adjunction of the roots of $X^{p^m}-X$) are variables with defining equations `hKU`, `hCL`, and $M_m$ is `M ⊔ CL m`. $\ell\ne p$ is `(l : F) ≠ 0`. Divisors are functions on `IsDedekindDomain.HeightOneSpectrum` of the relevant integral closure with finite support, $v_w(a)$ is `WithZero.log (w.valuation _ a)` (up to sign, which does not matter for the divisibility conditions), the residue field size is `Nat.card` of the quotient, and "$w$ lies over $v$" is written elementwise in $\overline F$ (`x ∈ v.asIdeal ↔ ∃ y ∈ w.asIdeal, (y : AlgebraicClosure F) = x`). The Dedekind and fraction-ring instances of these integral closures are taken as instance arguments inside the statement. The constant field of $F$ may be larger than $\mathbb F_q$. The statement is not vacuous: for $F=\mathbb F_q(t)$ and $M=F$ every divisor of $U=\mathbb A^1$ is principal with $m=1$, while for a field $F$ of positive genus $\operatorname{Pic}^0(X)$ is in general a nontrivial finite group, so the constant field extension $M_m$ is needed.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 and Chapter VI, §1; D. Mumford, Abelian Varieties, Oxford University Press (1970), §4 (an abelian variety over an algebraically closed field is a divisible group); A. Weil, Courbes algébriques et variétés abéliennes, Hermann (1948)

import Mathlib

set_option autoImplicit false

theorem FunctionField.geomPic_affine_divisible_and_geomPic0_divisible
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
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
              g = 1}, L.1) :
    (∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
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
            (l : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a)) ∧
    (∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
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
              ((l ^ n : ℕ) : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a)) := by
  sorry
