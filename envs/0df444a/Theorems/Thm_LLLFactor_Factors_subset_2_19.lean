-- Prove2me | Theorems.Thm_LLLFactor_Factors_subset_2_19
-- name    : LLLFactor.Factors.subset_2_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:29.625862+00:00
-- url     : https://prove2.me/theorems/4d902773-17d2-4e92-9715-e3ff192e81dd
-- title:
--   (2.19), proof of (2.16), p. 529 — if deg h₀ ≤ m, then |b_j| < (p^{kl}/|f|^m)^{1/n} for 1 ≤ j ≤ m + 1 − deg h₀
-- statement:
--   Assume the hypotheses of Proposition (2.13): the setting of Sect. 2, $h_0$ as in (2.5), $m\ge l$, a reduced basis $b_1,\dots,b_{m+1}$ for $L$, and (2.14). Suppose moreover that $\deg h_0\le m$. Then
--   $$|b_j|<\big(p^{kl}/|f|^m\big)^{1/n}\qquad\text{for }1\le j\le m+1-\deg h_0,$$
--   that is, with $J=\{j:\ |b_j|<(p^{kl}/|f|^m)^{1/n}\}$,
--   $$\text{(2.19)}\qquad\{1,2,\dots,m+1-\deg h_0\}\subset J.$$
--
--   The polynomials $h_0X^i$, $0\le i\le m-\deg h_0$, are $m+1-\deg h_0$ linearly independent short vectors of $L$; this inclusion is the other half of the squeeze in the proof of (2.16).
--
--   **Formalization Note** 0-based indices: the paper's $j\in\{1,\dots,m+1-\deg h_0\}$ is Lean's `j` with `j < m + 1 - h₀.natDegree`. The proof on the page uses Proposition (1.12) (the goal of mission I of this series), which is not an item of this mission.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 529, (2.19) in the proof of (2.16) Proposition

import Mathlib
import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial

namespace LLLFactor.Factors

theorem subset_2_19 {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : Fin (m + 1) → ℤ[X]) (hb : IsReducedBasisOfL p k h m b)
    (h214 : (2 : ℝ) ^ ((m : ℝ) * (f.natDegree : ℝ) / 2) *
        ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) *
        polyNorm f ^ (m + f.natDegree) < (p : ℝ) ^ (k * h.natDegree))
    (hdeg : h₀.natDegree ≤ m) :
    ∀ j : Fin (m + 1), (j : ℕ) < m + 1 - h₀.natDegree →
      polyNorm (b j) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ)) := by sorry

end LLLFactor.Factors
