-- Prove2me | Theorems.Thm_LLLFactor_Factors_prop_2_16
-- name    : LLLFactor.Factors.prop_2_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:40.017397+00:00
-- url     : https://prove2.me/theorems/c8f2a7ec-d9db-4523-9eb9-777a9b2f3846
-- title:
--   (2.16) Proposition, p. 528 — if t is the largest j with |b_j| < (p^{kl}/|f|^m)^{1/n}, then deg h₀ = m + 1 − t and h₀ = gcd(b₁, …, b_t)
-- statement:
--   Let the notation and the hypotheses be as in Proposition (2.13): $p$ prime, $k\ge1$, $f\in\mathbb Z[X]$ of degree $n>0$, $h\in\mathbb Z[X]$ satisfying (2.1)–(2.4) with $l=\deg h$, $h_0$ the irreducible factor of $f$ of (2.5), an integer $m\ge l$, a reduced basis $b_1,\dots,b_{m+1}$ for the lattice $L$ of (2.6), and
--   $$\text{(2.14)}\qquad p^{kl}>2^{mn/2}\binom{2m}{m}^{n/2}|f|^{m+n}.$$
--   Assume in addition that there is an index $j\in\{1,\dots,m+1\}$ with
--   $$\text{(2.17)}\qquad |b_j|<\big(p^{kl}/|f|^m\big)^{1/n},$$
--   and let $t$ be the largest such $j$. Then
--
--   1. $\deg h_0=m+1-t$;
--   2. $h_0=\gcd(b_1,b_2,\dots,b_t)$ (up to sign);
--   3. (2.17) holds for all $j$ with $1\le j\le t$.
--
--   This is the step that turns lattice basis reduction into a factoring algorithm: once $m$ is large enough, the short vectors of a reduced basis of $L$ cut out exactly the irreducible factor $h_0$, recovered by a gcd computation.
--
--   **Formalization Note** $t$ is the paper's 1-based index, $1\le t\le m+1$; the paper's $b_t$ is Lean's `b ⟨t - 1, _⟩`, and "$j>t$" is Lean's `t ≤ j`. "$t$ is the largest $j$ with (2.17)" is the pair of hypotheses: (2.17) holds at $t$, and fails at every later index. "$h_0=\gcd(b_1,\dots,b_t)$" is stated as: $h_0$ divides each of $b_1,\dots,b_t$, and every common divisor of $b_1,\dots,b_t$ divides $h_0$ (a gcd in $\mathbb Z[X]$ is determined up to the units $\pm1$). Real powers as in (2.13).
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), pp. 528–529, (2.16) Proposition

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem prop_2_16 {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : Fin (m + 1) → ℤ[X]) (hb : IsReducedBasisOfL p k h m b)
    (h214 : (2 : ℝ) ^ ((m : ℝ) * (f.natDegree : ℝ) / 2) *
        ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) *
        polyNorm f ^ (m + f.natDegree) < (p : ℝ) ^ (k * h.natDegree))
    (t : ℕ) (ht1 : 1 ≤ t) (htm : t ≤ m + 1)
    (htJ : polyNorm (b ⟨t - 1, by omega⟩) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ)))
    (htmax : ∀ j : Fin (m + 1), t ≤ (j : ℕ) →
      ¬ polyNorm (b j) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ))) :
    h₀.natDegree = m + 1 - t ∧
    ((∀ j : Fin (m + 1), (j : ℕ) < t → h₀ ∣ b j) ∧
      (∀ g : ℤ[X], (∀ j : Fin (m + 1), (j : ℕ) < t → g ∣ b j) → g ∣ h₀)) ∧
    (∀ j : Fin (m + 1), (j : ℕ) < t →
      polyNorm (b j) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ))) := by sorry

end LLLFactor.Factors
