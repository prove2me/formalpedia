-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_line_identity
-- name    : KhachiyanRound.BCD.line_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:29.563401+00:00
-- url     : https://prove2.me/theorems/dd959518-4673-4119-a539-2958049231ba
-- title:
--   (2.6), p. 309 — F((1 − τ)p + τe_j) = F(p) + (n − 1) ln(1 − τ) + ln(1 + τ(w_j − 1))
-- statement:
--   Let $a_1,\dots,a_m \in \mathbb{R}^n$, let $p \in S_F$, let $j$ be an index and $0 \le \tau < 1$. Moving from $p$ towards the vertex $e_j$ of the simplex changes the log-determinant by
--   $$F\big((1-\tau)p + \tau e_j\big) = F(p) + (n-1)\ln(1-\tau) + \ln\big(1 + \tau(w_j(p) - 1)\big),$$
--   where $F(p) = \ln\det A(p)$ and $w_j(p) = a_j^{\mathsf T}[A(p)]^{-1}a_j$.
--
--   This closed form of $F$ along a coordinate segment determines the BCD step length $\tau_r$ of (2.19) and gives the per-step increase (2.21).
--
--   **Formalization Note** The identity is stated in §2 under (2.1), (2.2) and $n\ge2$; it holds without them, and the Lean statement drops them.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 309, (2.6)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem line_identity {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (p : ι → ℝ) (hp : p ∈ SF a) (j : ι) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    F a ((1 - τ) • p + τ • Pi.single j 1) =
      F a p + ((n : ℝ) - 1) * Real.log (1 - τ) + Real.log (1 + τ * (w a p j - 1)) := by sorry
end KhachiyanRound.BCD
