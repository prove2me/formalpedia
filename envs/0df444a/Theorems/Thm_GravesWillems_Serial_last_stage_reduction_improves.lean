-- Prove2me | Theorems.Thm_GravesWillems_Serial_last_stage_reduction_improves
-- name    : GravesWillems.Serial.last_stage_reduction_improves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:20:46.09671+00:00
-- url     : https://prove2.me/theorems/771b6157-f0f5-46af-9a00-f34d8bd2f742
-- title:
--   Proof of the Result, case $k = N$ — reducing $B_N$ until the $N$-th constraint binds does not raise the objective
-- statement:
--   Let $(\Omega, \mu)$ be a probability space carrying a random demand path $d$ with $d(\cdot, \tau)$ integrable for every $\tau$, let $N \ge 1$, $T_1, \dots, T_N \in \mathbb{N}$, and let $D : \mathbb{N} \to \mathbb{R}$ be nondecreasing with $D(0) = 0$. Let $h$ be holding costs whose echelon holding costs are nonnegative, $h_i - h_{i+1} \ge 0$ for $1 \le i < N$ and $h_N \ge 0$.
--
--   Let $B^*$ be feasible for $\mathbf P^*$ with the first $N-1$ constraints of (A3) binding and the $N$-th strict. Let $B'$ equal $B^*$ except that the base stock of stage $N$ is reduced by the slack of the $N$-th constraint:
--   $$B'_N = B^*_N - \Bigl(B^*_1 + \dots + B^*_N - D(T_1 + \dots + T_N)\Bigr).$$
--   Then $B'$ is feasible for $\mathbf P^*$, satisfies every constraint of (A3) with equality, and for every period $t$ its objective value is at most that of $B^*$.
--
--   Together with the step for $k < N$, this completes the proof that some optimal solution binds all of (A3).
--
--   **Formalization Note** The paper's "nonnegative echelon holding costs" is read as $e_i = h_i - h_{i+1} \ge 0$ for $i = 1, \dots, N$ with $h_{N+1} := 0$; this step is where $e_N = h_N \ge 0$ is used ("with no penalty to the objective function"). $D(0) = 0$ is the paper's convention (§2, p. 70), used when $N = 1$.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, p. 82, Appendix, proof of the Result (the case k = N)

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP
open MeasureTheory

namespace GravesWillems.Serial

/-- Appendix, proof of the Result, the case `k = N` (Graves–Willems 2000, p. 82): let `B*` be
feasible for `P*` with the constraints (A3) with index `1, …, N − 1` binding and the `N`-th
strict. Reducing the base stock of stage `N` by the slack of the `N`-th constraint gives a
feasible vector that binds every constraint (A3) and, when `D(0) = 0`, `D` is nondecreasing, the
echelon holding costs `hᵢ − h_{i+1}` (`1 ≤ i < N`) are nonnegative and `h_N ≥ 0`, has objective
value no greater than that of `B*` at every period `t`. -/
theorem last_stage_reduction_improves {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (hN : 1 ≤ N) (T : ℕ → ℕ) (D : ℕ → ℝ) (hD0 : D 0 = 0) (hD : Monotone D)
    (h : ℕ → ℝ) (he : ∀ i ∈ Finset.Ico 1 N, 0 ≤ h i - h (i + 1)) (hhN : 0 ≤ h N)
    (B : ℕ → ℝ) (hB : Feasible N T D B)
    (hbind : ∀ i ∈ Finset.Ico 1 N,
      ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m))
    (hstrict : D (∑ m ∈ Finset.Icc 1 N, T m) < ∑ m ∈ Finset.Icc 1 N, B m) :
    Feasible N T D (Function.update B N
        (B N - (∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m)))) ∧
    (∀ i ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 i, Function.update B N
          (B N - (∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m))) m
        = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ t : ℤ,
      objective μ d N T h (Function.update B N
          (B N - (∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m)))) t
        ≤ objective μ d N T h B t := by sorry

end GravesWillems.Serial
