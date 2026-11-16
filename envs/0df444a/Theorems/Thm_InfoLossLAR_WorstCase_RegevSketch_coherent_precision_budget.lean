-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_coherent_precision_budget
-- name    : InfoLossLAR.WorstCase.RegevSketch.coherent_precision_budget
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:17:09.650824+00:00
-- url     : https://prove2.me/theorems/fa81be66-b79d-4747-a97a-b6299579f191
-- title:
--   Bit-length precision budget for a coherent hybrid bound
-- statement:
--   Let $T,B$ be nonnegative integers, and let $\varepsilon_i$ be real step-error bounds for $0\le i<T$. Put
--
--   $$
--   k=3+\operatorname{size}(T+1)+\operatorname{size}(B+1).
--   $$
--
--   If each $\varepsilon_i\le 2^{-2k}$, then
--
--   $$
--   4\sum_{i=0}^{T-1}\sqrt{\varepsilon_i}\le\frac{1}{2(B+1)}.
--   $$
--
--   This allocates at most half of an inverse numerical budget to the square-root losses of the coherent hybrid bound. It is a mathematical precision bound; it does not construct a decoder, prove its per-step error, or establish a machine implementation of precision selection.
--
--   **Formalization Note.** `Nat.size` is binary length and the theorem uses Lean's real square root.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemma 3.3, pp. 18–19. This explicit numerical precision allocation is a separately derived auxiliary bound for the formal hybrid error estimate, not a verbatim theorem in the source.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem InfoLossLAR.WorstCase.RegevSketch.coherent_precision_budget (steps budget : ℕ) (failure : ℕ → ℝ)
    (hfailure : ∀ i < steps,
      failure i ≤ (1 / (2 : ℝ) ^ (3 + Nat.size (steps+1) + Nat.size (budget+1))) ^ 2) :
    (∑ i ∈ Finset.range steps, 4 * Real.sqrt (failure i)) ≤
      1 / (2 * ((budget : ℝ)+1)) := by sorry
