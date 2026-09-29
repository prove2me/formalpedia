-- Prove2me | Theorems.Thm_GravesWillems_Serial_transfer_step_improves
-- name    : GravesWillems.Serial.transfer_step_improves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:20:05.533417+00:00
-- url     : https://prove2.me/theorems/7c526d3c-0171-4284-bf38-0bcd5fb272ad
-- title:
--   Eqs. (A7)–(A8) — one improving step for $k < N$ binds the $k$-th constraint without raising the objective
-- statement:
--   Let $(\Omega, \mu)$ be a probability space carrying a random demand path $d$ with $d(\cdot, \tau)$ integrable for every $\tau$, let $T_1, \dots, T_N \in \mathbb{N}$, and let $D : \mathbb{N} \to \mathbb{R}$ be nondecreasing with $D(0) = 0$. Let $h$ be holding costs with nonnegative echelon holding costs $e_i = h_i - h_{i+1} \ge 0$ for $1 \le i < N$.
--
--   Let $B^*$ be feasible for $\mathbf P^*$ and $1 \le k < N$, such that the first $k-1$ constraints of (A3) are binding and the $k$-th is strict:
--   $$B^*_1 + \dots + B^*_i = D(T_1 + \dots + T_i)\ (i = 1, \dots, k-1), \qquad B^*_1 + \dots + B^*_k > D(T_1 + \dots + T_k).$$
--   Put
--   $$\Delta = B^*_k - D\Bigl(\sum_{i=1}^k T_i\Bigr) + D\Bigl(\sum_{i=1}^{k-1} T_i\Bigr)$$
--   and let $B^{**}$ equal $B^*$ except $B^{**}_k = B^*_k - \Delta$, $B^{**}_{k+1} = B^*_{k+1} + \Delta$. Then
--   1. $B^{**}$ is feasible for $\mathbf P^*$;
--   2. $B^{**}$ satisfies the first $k$ constraints of (A3) with equality;
--   3. for every period $t$, the objective of $\mathbf P^*$ at $B^{**}$ is at most its value at $B^*$.
--
--   Item 3 combines $\sum_i h_i B^{**}_i = -e_k \Delta + \sum_i h_i B^*_i$ (A7) with $-\sum_{i=2}^N e_{i-1} E[Q_i]^{**} \le -\sum_{i=2}^N e_{i-1} E[Q_i]^* + e_k \Delta$ (A8). Iterating this step is the core of the proof of the Result.
--
--   **Formalization Note** "The echelon holding costs are nonnegative" is read, for this step, as $e_i \ge 0$ for $1 \le i < N$ (only $e_1, \dots, e_{N-1}$ enter the objective). $D(0) = 0$ is the paper's convention (§2, p. 70) and is used at $k = 1$, where the empty sum gives $D(0)$. The objective is evaluated at a fixed period $t$.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, pp. 81-82, Appendix, proof of the Result, definition of B** (p. 81), Eqs. (A7) and (A8) (p. 82)

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP
open MeasureTheory

namespace GravesWillems.Serial

/-- Eqs. (A7)–(A8) of Graves–Willems 2000 (Appendix, pp. 81–82): let `B*` be feasible for `P*`,
`1 ≤ k < N`, the constraints (A3) with index `1, …, k − 1` binding and the `k`-th strict. With
`Δ = B*_k − D(Σ_{i=1}^k Tᵢ) + D(Σ_{i=1}^{k−1} Tᵢ)`, the vector `B**` obtained by moving `Δ` from
stage `k` to stage `k + 1` is feasible, binds the constraints `1, …, k`, and, when `D(0) = 0`,
`D` is nondecreasing and the echelon holding costs `e_i = hᵢ − h_{i+1}` (`1 ≤ i < N`) are
nonnegative, has objective value no greater than that of `B*` at every period `t`. -/
theorem transfer_step_improves {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (hD0 : D 0 = 0) (hD : Monotone D)
    (h : ℕ → ℝ) (he : ∀ i ∈ Finset.Ico 1 N, 0 ≤ h i - h (i + 1))
    (B : ℕ → ℝ) (hB : Feasible N T D B) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (hbind : ∀ i ∈ Finset.Ico 1 k,
      ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m))
    (hstrict : D (∑ m ∈ Finset.Icc 1 k, T m) < ∑ m ∈ Finset.Icc 1 k, B m) :
    Feasible N T D (transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
        + D (∑ m ∈ Finset.Icc 1 (k - 1), T m))) ∧
    (∀ i ∈ Finset.Icc 1 k,
      ∑ m ∈ Finset.Icc 1 i, transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
          + D (∑ m ∈ Finset.Icc 1 (k - 1), T m)) m
        = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ t : ℤ,
      objective μ d N T h (transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
          + D (∑ m ∈ Finset.Icc 1 (k - 1), T m))) t
        ≤ objective μ d N T h B t := by sorry

end GravesWillems.Serial
