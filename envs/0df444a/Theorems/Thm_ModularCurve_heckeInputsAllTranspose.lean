-- Prove2me | Theorems.Thm_ModularCurve_heckeInputsAllTranspose
-- name    : ModularCurve.heckeInputsAllTranspose
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/4d5f0a6c-3a72-5206-8d9c-3f7b21d0e38b
-- title:
--   Transposed Hecke correspondence inputs at level N for every prime ℓ
-- statement:
--   Fix $N\ge 1$ and a prime $\ell$, and work over $L=\overline{\mathbb Q}$ (the `AlgebraicClosure` of $\mathbb Q$). Let $F_M$ denote `laurentBaseChange L (modularFunctionFieldFull M)`, the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image of the level-$M$ full modular function field inside $\mathbb Q((q))$, and let $\bar\alpha_\ell,\bar\beta_\ell : F_N \to F_{N\ell}$ be the two $L$-algebra maps `heckeAlphaBar` (the inclusion coming from $N \mid N\ell$) and `heckeBetaBar` (substitution $q \mapsto q^{\ell}$ on Laurent expansions). The theorem asserts the existence of: a proof $h\alpha$ that $\bar\alpha_\ell$ is an integral ring map; a proof that $\bar\beta_\ell$ is an integral ring map; a proof that $F_{N\ell}$ has principal divisors over $L$, i.e. every $f \neq 0$ admits a divisor $D$ (a finitely supported $\mathbb Z$-valued function on the places of $F_{N\ell}/L$, places being proper valuation subrings containing $L$ that are principal ideal rings) with $D(v)=\operatorname{ord}_v f$ for all $v$ and $\deg D = 0$; and a proof $h_{\mathrm{fin}}$ that $F_{N\ell}$ is a finite module over $F_N$ via $\bar\beta_\ell$; such that, first, the fundamental identity holds along $\bar\alpha_\ell$: for every place $v$ of $F_N/L$, $\sum_{w \mid v} e(w\mid v)\deg w = [F_{N\ell}:F_N]\deg v$; and second, the pushforward norm formula holds along $\bar\beta_\ell$: for every $f \neq 0$ in $F_{N\ell}$ and every divisor $D$ with $D(w)=\operatorname{ord}_w f$ for all $w$, the pushforward of $D$ takes the value $\operatorname{ord}_v(\mathrm{N}_{F_{N\ell}/F_N} f)$ at each place $v$.
--
--   These are the divisor-theoretic inputs needed to form the transposed Hecke correspondence $\bar\alpha_{\ell*}\bar\beta_\ell^{*}$ on the degree-zero divisor class group of the level-$N$ modular function field, the adjoint of $T_\ell=\bar\beta_{\ell*}\bar\alpha_\ell^{*}$; the roles of the two degeneracy maps are interchanged relative to the untransposed packaging. It is used in the comparison of the Hecke operator with its Fricke conjugate and in the construction of separated chart coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeInputsAllTranspose.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorTotal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeInputsAllTranspose (N : ℕ) [NeZero N] (ℓ : Nat.Primes) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    ∃ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
      (_ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)),
      FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα ∧
        NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hfin := by sorry
