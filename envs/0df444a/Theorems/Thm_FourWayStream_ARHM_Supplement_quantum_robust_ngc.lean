-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_quantum_robust_ngc
-- name    : FourWayStream.ARHM.Supplement.quantum_robust_ngc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:07:00.697203+00:00
-- url     : https://prove2.me/theorems/d38e838f-fa67-4fa6-a48e-8c0699c67209
-- title:
--   Theorem 7.2 — quantum robust Noisy Gap Cycle needs $\Omega(n)$ qubits for $k\ge1600\log n$
-- statement:
--   There are universal constants $c>0$ and $n_0$ such that for every admissible $(n,k)$ ($k\ge3$, $4k\mid n$) with $n\ge n_0$ and $k\ge1600\log_2n$, every robust one-way quantum protocol for $\mathrm{NGC}_{n,k}$ with error at most $1/3$ sends
--   $$q\ge c\,n$$
--   qubits. Robust means that the error guarantee holds for every promise graph, averaged over the fair independent edge split and the protocol's randomness.
--
--   This is the quantum analogue of the classical robust bound of Assadi and Sundaresan; via Theorem 7.3 it shows that for long cycles neither random order nor quantum memory helps.
--
--   **Formalization Note** "Sufficiently large admissible $(n,k)$" is $n\ge n_0$ (with $k\le n/4$, $(n,k)$ is large iff $n$ is). Every admissible $k$ is covered, not only $k\equiv1\pmod 3$.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: for all sufficiently large admissible (n, k) … Ω(n) qubits → ∃ c > 0 and n₀ (universal) such that n ≥ n₀, k ≥ 1600 log₂ n imply c·n ≤ q; reason: the standard meaning of Ω/O with the constant and threshold quantified before every varying parameter, as §4 uses them
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.33, Theorem 7.2 (proof p.37)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 7.2 (Quantum robust Noisy Gap Cycle), p.33. There are universal `c > 0` and `n₀` such
that for every admissible `(n, k)` with `n ≥ n₀` and `k ≥ 1600 log₂ n`, every robust one-way quantum
protocol for `NGC_{n,k}` with error at most `1/3` and message dimension at most `2^q` has
`q ≥ c n`: it sends `Ω(n)` qubits. -/
theorem quantum_robust_ngc :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n k : ℕ, Admissible n k → n₀ ≤ n →
      1600 * Real.logb 2 n ≤ k → ∀ {nR : ℕ} (P : ShareProtocol (Fin n) nR), P.Valid →
        RobustNGCErrorLE P k (1 / 3) → ∀ q : ℕ, P.d ≤ 2 ^ q → c * n ≤ q := by sorry

end FourWayStream.ARHM.Supplement
