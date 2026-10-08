-- Prove2me | Theorems.Thm_FracPackCover_Covering_theorem_3_5
-- name    : FracPackCover.Covering.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:53.711181+00:00
-- url     : https://prove2.me/theorems/2d593b57-014e-4773-b512-d6929b889c93
-- title:
--   Theorem 3.5 — IMPROVE-COVER stops within $2+20\rho\varepsilon^{-3}\ln(4m/\varepsilon)$ calls, and $2+196\rho\varepsilon^{-2}\ln(4m/\varepsilon)$ from a $6\varepsilon$-optimal start
-- statement:
--   Let $A\ge0$, $b>0$, $P$ be covering data, $\rho>0$ a width bound, and let subroutine (7) be an exact maximization oracle. Let $0<\varepsilon<1$ and $x\in P$ with $\lambda(x)>0$.
--   1. IMPROVE-COVER$(x,\varepsilon)$ terminates, and it makes at most
--   $$2+20\,\rho\,\varepsilon^{-3}\ln\frac{4m}{\varepsilon}$$
--   calls to subroutine (7); the number of evaluations of its while-test obeys the same bound.
--   2. If moreover $\varepsilon\le\frac1{12}$ and the initial solution is $6\varepsilon$-optimal, i.e. $(1-6\varepsilon)\lambda(x')\le\lambda(x)$ for every $x'\in P$, then IMPROVE-COVER$(x,\varepsilon)$ terminates after at most
--   $$2+196\,\rho\,\varepsilon^{-2}\ln\frac{4m}{\varepsilon}$$
--   calls (and as many while-tests).
--
--   These are the per-call costs from which the total cost of the covering algorithm (Theorem 3.7) is assembled: the first bound for the calls with $\varepsilon=1/6$, the second for the $\varepsilon$-scaling phases.
--
--   **Formalization Note** The paper writes $O(\varepsilon^{-3}\rho\log(m\varepsilon^{-1}))$ and $O(\varepsilon^{-2}\rho\log(m\varepsilon^{-1}))$ iterations; its proof yields at most $1+20\rho\varepsilon^{-3}\ln(4m/\varepsilon)$ and $1+196\rho\varepsilon^{-2}\ln(4m/\varepsilon)$ updates, and one more oracle call for the final test. The second sentence of the printed theorem names IMPROVE-PACKING, a misprint for IMPROVE-COVER, which is what is stated here. Termination is asserted: the run with that many while-tests returns a result.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 20, Theorem 3.5

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover

namespace FracPackCover.Covering

/-- Theorem 3.5 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 20), with the explicit constants
of its proof. Let `0 < ε < 1`, `x ∈ P` with `λ(x) > 0`, `ρ` a width bound and `orc` an exact
maximization oracle.
1. IMPROVE-COVER(x, ε) stops within `B₁ = 2 + 20 ρ ε⁻³ ln(4 m ε⁻¹)` evaluations of its while-test
   and makes at most `B₁` oracle calls (the paper writes `O(ε⁻³ ρ log(m ε⁻¹))` iterations).
2. If moreover `ε ≤ 1/12` and `x` is `6ε`-optimal (`(1 − 6ε) λ(x') ≤ λ(x)` for every `x' ∈ P`), it
   stops within `B₂ = 2 + 196 ρ ε⁻² ln(4 m ε⁻¹)` tests and makes at most `B₂` oracle calls (the paper
   writes `O(ε⁻² ρ log(m ε⁻¹))`; its second sentence names IMPROVE-PACKING, a misprint for
   IMPROVE-COVER). -/
theorem theorem_3_5 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (x : Fin n → ℝ) (hx : x ∈ P) (hlam : 0 < lam A b x) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ x' : Fin n → ℝ, ∃ c : ℕ,
      improveCover A b orc ρ ε x ⌈2 + 20 * ρ * ε⁻¹ ^ 3 * Real.log (4 * m * ε⁻¹)⌉₊ = some (x', c) ∧
      (c : ℝ) ≤ 2 + 20 * ρ * ε⁻¹ ^ 3 * Real.log (4 * m * ε⁻¹)) ∧
    (ε ≤ 1 / 12 → (∀ x' ∈ P, (1 - 6 * ε) * lam A b x' ≤ lam A b x) →
      ∃ x' : Fin n → ℝ, ∃ c : ℕ,
        improveCover A b orc ρ ε x ⌈2 + 196 * ρ * ε⁻¹ ^ 2 * Real.log (4 * m * ε⁻¹)⌉₊ =
          some (x', c) ∧
        (c : ℝ) ≤ 2 + 196 * ρ * ε⁻¹ ^ 2 * Real.log (4 * m * ε⁻¹)) := by sorry

end FracPackCover.Covering
