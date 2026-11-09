-- Prove2me | Theorems.Thm_LocalPush_theorem_4_1
-- name    : LocalPush.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:12.094854+00:00
-- url     : https://prove2.me/theorems/37c6b19f-a635-409b-a524-a1371688a079
-- title:
--   Theorem 4.1 — SDD solver [JS25] in $O(\mathrm{nnz}(S)(\log\log N)^{13}\log(1/(\mu\delta)))$ time (corrected: logarithms clamped at 1)
-- statement:
--   There are a program $P$ of the machine `LocalPush.Machine` and a constant $C>0$ with the following property. Let $N\ge1$, let $S\in\mathbb R^{N\times N}$ be a positive definite SDD matrix given by the list of its $k=\mathrm{nnz}(S)$ nonzero entries in any order, let $b\in\mathbb R^N$, and let $\mu,\delta\in(0,1)$. Then:
--
--   1. on every coin tape, $P$ halts within
--   $$C\cdot\mathrm{nnz}(S)\cdot \mathrm L(\mathrm L(N))^{13}\cdot\mathrm L\big(1/(\mu\delta)\big)$$
--   steps, where $\mathrm L(x)=\max\{1,\log x\}$;
--   2. on a measurable set of tapes of probability at least $1-\delta$, its output $\tilde x$ satisfies
--   $$\|\tilde x-S^{-1}b\|_S\le\mu\,\|S^{-1}b\|_S.\tag{6}$$
--
--   The active-set algorithm calls this solver once per iteration; its nearly linear running time is what turns the bound on the number of iterations into the time bound of Theorem 1.2.
--
--   **Formalization Note** This states what the paper says of [JS25], which was not consulted. The solver receives the empty graph and does not use the oracle.
--
--   Differences from the source:
--   - correction: O(nnz(S)(log log N)^13 log(1/(µδ))) → C·nnz(S)·L(L(N))^13·L(1/(µδ)) with L(x) = max{1, log x}; reason: the printed bound is false: (log log N)^13 is negative at N = 2 and 0 at N = e, and log(1/(µδ)) tends to 0 as µδ tends to 1, while every run needs at least one step; when log log N ≥ 1 and log(1/(µδ)) ≥ 1 the clamped bound is the printed one
--   - reading: "runs in O(·) time" for "a randomized algorithm", with "a version of SDD solvers with a deterministic running-time bound" (p.15) → one admissible program of LocalPush.Machine, halting within the bound on every coin tape; (6) on a measurable set of tapes of probability ≥ 1 − δ; reason: the paper names no machine; the preceding paragraph says the running-time bound is deterministic
--   - encoding: a positive definite SDD matrix S ∈ ℝ^{N×N} and b ∈ ℝ^N given to the algorithm → N ≥ 1; S given as the injective list of its k = nnz(S) nonzero entries in any order, with b, µ, δ in a fixed memory layout; output x̃(i) at real address −1 − i; reason: the input must be laid out in memory; N = 0 is the empty matrix, where log log N is undefined
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §4, Theorem 4.1, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_LocalPush_SDD
import Definitions.Def_LocalPush_Layout

open Finset Matrix

namespace LocalPush

/-- **Theorem 4.1 (SDD solver [JS25]) (corrected: logarithms clamped at 1).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §4, Theorem 4.1, p.15 (PDF p.15).

"There is a randomized algorithm SDDSolve(S, b, µ, δ) that, given a positive definite SDD matrix S ∈ ℝ^{N×N}, a
vector b ∈ ℝ^N, an accuracy parameter µ ∈ (0, 1), and a failure probability δ ∈ (0, 1), runs in
O(nnz(S) (log log N)^13 log(1/(µδ))) time and with probability at least 1 − δ returns a vector x̃ ∈ ℝ^N such that
‖x̃ − S⁻¹b‖_S ≤ µ‖S⁻¹b‖_S. (6)" The paragraph before it: "We state below a version of SDD solvers with a
deterministic running-time bound".

There are one admissible program `P` of the machine `LocalPush.Machine` and a constant `C > 0` such that, for
every `N ≥ 1`, every positive definite SDD matrix `S ∈ ℝ^{N×N}` given by the list of its `k = nnz(S)` nonzero
entries in any order, every `b ∈ ℝ^N` and all `µ, δ ∈ (0, 1)`: on every coin tape `P` halts within
`C · k · L(L(N))^13 · L(1/(µδ))` steps, where `L(x) = max{1, log x}`; and on a measurable set of tapes of
probability at least `1 − δ`, the output `x̃` (real memory at `−1 − i`) satisfies (6).

**Formalization Note.**
* This is what this paper says of [JS25]; [JS25] itself was not consulted. The solver runs on the empty graph,
  so its oracle instructions are useless; its randomness is the fair-coin tape.
* `(log log N)^13` is negative at `N = 2` and `0` at `N = e`, so each logarithm is clamped at `1`. For large `N`
  and small `µδ` this is the printed bound.
* The listing is exactly the nonzero entries (injective, each listed entry nonzero, each nonzero entry listed),
  so `k = nnz(S)`. -/
theorem theorem_4_1 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℝ), 1 ≤ N → S.PosDef → IsSDD S →
      ∀ (k : ℕ) (ent : Fin k → Fin N × Fin N), Function.Injective ent →
        (∀ j, S (ent j).1 (ent j).2 ≠ 0) → (∀ i l, S i l ≠ 0 → ∃ j, ent j = (i, l)) →
      ∀ (b : Fin N → ℝ) (μ δ : ℝ), 0 < μ → μ < 1 → 0 < δ → δ < 1 →
        (∀ ω : ℕ → Bool, ∃ t : ℕ,
          (run P emptyGraph (sddInput N k ent S b μ δ) ω t).halted = true ∧
          ((run P emptyGraph (sddInput N k ent S b μ δ) ω t).work : ℝ) ≤
            C * k * clog (clog N) ^ 13 * clog (1 / (μ * δ))) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ coinTape E ∧
          ∀ ω ∈ E, ∀ t : ℕ, (run P emptyGraph (sddInput N k ent S b μ δ) ω t).halted = true →
            enorm S (outVec N (run P emptyGraph (sddInput N k ent S b μ δ) ω t) - S⁻¹ *ᵥ b) ≤
              μ * enorm S (S⁻¹ *ᵥ b) := by sorry

end LocalPush
