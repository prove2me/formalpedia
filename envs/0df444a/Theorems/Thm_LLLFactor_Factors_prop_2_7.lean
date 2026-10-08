-- Prove2me | Theorems.Thm_LLLFactor_Factors_prop_2_7
-- name    : LLLFactor.Factors.prop_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:21:14.417988+00:00
-- url     : https://prove2.me/theorems/334435d4-d9d5-4027-b88c-a1b3941aae3f
-- title:
--   (2.7) Proposition, p. 527 — if b ∈ L and p^{kl} > |f|^m·|b|ⁿ, then h₀ divides b; in particular gcd(f, b) ≠ 1
-- statement:
--   Assume the setting of Sect. 2 ($p$ prime, $k\ge1$, $\deg f=n>0$, $h$ satisfying (2.1)–(2.4), $l=\deg h$), an integer $m\ge l$, the lattice $L$ of (2.6), and $h_0$ as in (2.5). Let $b\in L$ satisfy
--   $$\text{(2.8)}\qquad p^{kl}>|f|^m\cdot|b|^n.$$
--   Then $b$ is divisible by $h_0$ in $\mathbb Z[X]$, and in particular $\gcd(f,b)\neq1$: $f$ and $b$ have a common divisor in $\mathbb Z[X]$ that is not a unit.
--
--   This is the bridge from short lattice vectors to factors: any element of $L$ that is short enough must share the factor $h_0$ with $f$.
--
--   **Formalization Note** "$\gcd(f,b)\ne1$" is stated as the existence of a common divisor of $f$ and $b$ that is not a unit of $\mathbb Z[X]$ (the units are $\pm1$), which avoids choosing a normalisation of the gcd. The standing assumptions are bundled in `IsSetting p k f h`.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 527, (2.7) Proposition

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem prop_2_7 {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : ℤ[X]) (hbL : b ∈ latticeL p k h m)
    (h28 : polyNorm f ^ m * polyNorm b ^ f.natDegree < (p : ℝ) ^ (k * h.natDegree)) :
    h₀ ∣ b ∧ ∃ d : ℤ[X], d ∣ f ∧ d ∣ b ∧ ¬ IsUnit d := by sorry

end LLLFactor.Factors
