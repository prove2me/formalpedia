-- Prove2me | Theorems.Thm_LLLFactor_Factors_prop_2_13
-- name    : LLLFactor.Factors.prop_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:22:10.714098+00:00
-- url     : https://prove2.me/theorems/c53c905c-acbb-4c8f-adb3-0859c6de7d4c
-- title:
--   (2.13) Proposition, p. 528 — for a reduced basis of L and p^{kl} > 2^{mn/2}C(2m,m)^{n/2}|f|^{m+n}: deg h₀ ≤ m ⇔ |b₁| < (p^{kl}/|f|^m)^{1/n}
-- statement:
--   Let $p,k,f,n,h,l$ be as in the setting of Sect. 2, $h_0$ as in (2.5), and $m\ge l$, $L$ as in (2.6). Suppose that $b_1,b_2,\dots,b_{m+1}$ is a reduced basis for $L$ (see (1.4) and (1.5)), and that
--   $$\text{(2.14)}\qquad p^{kl}>2^{mn/2}\binom{2m}{m}^{n/2}|f|^{m+n}.$$
--   Then $\deg h_0\le m$ if and only if
--   $$\text{(2.15)}\qquad |b_1|<\big(p^{kl}/|f|^m\big)^{1/n}.$$
--
--   So the first vector of a reduced basis decides whether the irreducible factor $h_0$ has degree at most $m$; this is the test the factoring algorithm runs for increasing $m$.
--
--   **Formalization Note** The paper's $b_1$ is Lean's `b 0`. The powers $2^{mn/2}$, $\binom{2m}{m}^{n/2}$ and $(\cdot)^{1/n}$ are real powers with real exponents; $p^{kl}$ and $|f|^{m+n}$ are natural-number powers.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 528, (2.13) Proposition

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem prop_2_13 {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : Fin (m + 1) → ℤ[X]) (hb : IsReducedBasisOfL p k h m b)
    (h214 : (2 : ℝ) ^ ((m : ℝ) * (f.natDegree : ℝ) / 2) *
        ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) *
        polyNorm f ^ (m + f.natDegree) < (p : ℝ) ^ (k * h.natDegree)) :
    h₀.natDegree ≤ m ↔
      polyNorm (b ⟨0, Nat.succ_pos m⟩) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ)) := by sorry

end LLLFactor.Factors
