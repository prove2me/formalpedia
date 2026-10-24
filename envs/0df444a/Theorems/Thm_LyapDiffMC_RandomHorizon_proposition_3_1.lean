-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_proposition_3_1
-- name    : LyapDiffMC.RandomHorizon.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:47.558982+00:00
-- url     : https://prove2.me/theorems/67d03b22-9311-4877-9b4f-5e3bcd05c1d1
-- title:
--   Proposition 3.1, p. 11 — if Qv ≤ v − f for a non-negative kernel Q, f ≥ 0 and finite v ≥ 0, then Σₙ Qⁿf ≤ v
-- statement:
--   Let $Q=(Q(x,dy):x,y\in C)$ be a non-negative kernel on a measurable space $C$, and let $f:C\to[0,\infty)$ be measurable. Suppose $v:C\to[0,\infty)$ is a finite-valued measurable function with
--   $$Qv\le v-f,\tag{3.15}$$
--   that is, $\int v(y)Q(x,dy)\le v(x)-f(x)$ for every $x\in C$. Then
--   $$\sum_{n=0}^\infty Q^nf\le v,\tag{3.16}$$
--   where $Q^0(x,dy)=\delta_x(dy)$ and $Q^{n+1}(x,A)=\int Q^n(x,dy)Q(y,A)$.
--
--   This comparison bound drives the proof of Theorem 3.1. Applied to (3.11) it gives $\sum_nK^n(\theta)|\tilde f(\theta)|\le v_0$. Applied to (3.12) it bounds the $G$-integrals that control the derivative.
--
--   **Formalization Note** The space $C$ is an arbitrary measurable space $S$, and the kernel need not be finite. $f$ and $v$ are $[0,\infty]$-valued with $v$ finite everywhere, and (3.15) is written as $Qv+f\le v$.
--
--   Differences from the source:
--   - encoding: Q = (Q(x, dy) : x, y ∈ C) a non-negative kernel, f : C → ℝ₊, v : C → ℝ₊ finite-valued → Q : Kernel S S on an arbitrary measurable space S (playing C), f v : S → ℝ≥0∞ measurable, v x ≠ ⊤; reason: C is itself a measurable space; (3.15) with v finite forces f ≤ v < ∞, so allowing f to take the value ∞ adds no instance; measurability is needed for Qv and Qⁿf to be defined
--   - encoding: Qv ≤ v − f (3.15) → ∫ v dQ(x, ·) + f(x) ≤ v(x) for all x, in ℝ≥0∞; reason: equivalent because v is finite
--   - encoding: Q⁰ = I, Qⁿ = QQⁿ⁻¹ → Qpow Q 0 = Kernel.id, Qpow Q (n+1) = Q ∘ₖ Qpow Q n; reason: the same kernel (composition is associative); Σₙ Qⁿf as a sum in ℝ≥0∞
-- source:
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 11, Proposition 3.1, (3.15)–(3.16)

import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Proposition 3.1 (p. 11). For a non-negative kernel `Q`, a non-negative `f` and a
finite-valued non-negative `v` with `Qv ≤ v - f` (3.15), `Σₙ Qⁿ f ≤ v` (3.16). The measurable
space `S` plays the role of the paper's `C`; (3.15) is written additively, `Qv + f ≤ v`, which is
equivalent because `v` is finite. -/
theorem proposition_3_1 {S : Type*} [MeasurableSpace S] (Q : Kernel S S)
    (f v : S → ℝ≥0∞) (hf : Measurable f) (hv : Measurable v) (hv_fin : ∀ x, v x ≠ ⊤)
    (h315 : ∀ x, ∫⁻ y, v y ∂(Q x) + f x ≤ v x) :
    ∀ x, ∑' n, ∫⁻ y, f y ∂(Qpow Q n x) ≤ v x := by sorry

end LyapDiffMC.RandomHorizon
