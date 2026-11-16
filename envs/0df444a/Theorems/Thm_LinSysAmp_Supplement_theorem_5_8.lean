-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_5_8
-- name    : LinSysAmp.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:51:30.971776+00:00
-- url     : https://prove2.me/theorems/151dd68d-7f12-4587-93d8-e80fc15537b5
-- title:
--   Theorem 5.8 — hardness self-amplification for the parity of triangles (Figure 6)
-- statement:
--   Let $n\ge1$ and let $O$ be an algorithm on graphs with $n$ vertices, taking time $T$ per call, such that
--   $$\Pr_{A\leftarrow S_n,\,O}[O(A)=\tau(A)]\ge\tfrac12+\varepsilon$$
--   for some $\varepsilon>0$, where $S_n$ is the set of adjacency matrices (symmetric, zero diagonal, over $\mathbb F_2$) and $\tau(A)$ the parity of the number of triangles. For every $0<\delta<1/2$, the algorithm $D$ of Figure 6 with
--   $$t=\lceil\varepsilon^{-2}\log(1/\delta)\rceil$$
--   makes $t$ calls to $O$, all on graphs with $n$ vertices, runs in time $O((T+n^2)\varepsilon^{-2}\log(1/\delta))$, and outputs $\tau(A)$ with probability at least $1-\delta$ when $A\leftarrow S_n$.
--
--   This amplifies any non-trivial advantage for the parity of triangles in $G(n,1/2)$ to success $1-\delta$ on average, with $O(\varepsilon^{-2})$ overhead.
--
--   **Formalization Note** Figure 6 is defined at the level of output distributions. The theorem states its average-case guarantee, and that a program of the oracle machine over $\mathbb F_2$ realizes it: on every $A\in S_n$ and every oracle the program's output distribution equals that of Figure 6, every run makes exactly $t$ calls, and every run halts with at most $C n^2\varepsilon^{-2}\log(1/\delta)$ field operations. The program and $C$ are chosen before $n$, $\varepsilon$, $\delta$ and the oracle.
--
--   Differences from the source:
--   - encoding: "the algorithm D of Figure 6 … makes t calls and runs in time O((T + n²)ε⁻² log(1/δ))" → the PMF-level Figure 6 has the success guarantee, and one machine program has the same output distribution on every A ∈ S_n and oracle, exactly t calls and at most C·n²·ε⁻²·log(1/δ) operations on every run; reason: an algorithm's running time is only defined on a machine; the program is tied to Figure 6 by equality of output distributions
--   - reading: an O(·) bound with an unnamed constant and "there is an algorithm" → one absolute constant C, chosen before the field, and one program per field chosen before n, the parameters and the oracle; reason: the proof's constants are absolute and the reduction is black-box and uniform; this is the standard reading of O(·)
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed advantage ε → they hold for every oracle; only the success guarantee assumes the advantage ε; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: ε unconstrained above → ε ≤ 1/2 added; reason: the hypothesis 1/2 + ε ≤ Pr[O(A) = τ(A)] ≤ 1 already forces it; without it the unconditional cost bound could not be met for large ε
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 5.8 and Figure 6, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_Triangles

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

/-- Theorem 5.8 (Hardness self-amplification for the parity of triangles), p.31 (PDF p.33).
Couteau, Melissaris, Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained
Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let O be a time-T algorithm such that Pr_{A←S_n,O}[O(A) = τ(A)] ≥ 1/2 + ε, for some ε > 0. For
every 0 < δ < 1/2, the algorithm D of Figure 6 with t = ⌈ε⁻² log(1/δ)⌉ makes t calls to O, runs in
time O((T + n²)ε⁻² log(1/δ)), and outputs τ(A) with probability at least 1 − δ when A ← S_n. All
calls are made on graphs with n vertices."

**Formalization Note.**
* *The algorithm of Figure 6* is `figure6 O t` (its output distribution, defined at the level of
  probability mass functions). The theorem states (a) its guarantee, averaged over `A ← S_n`
  (average case), and (b) that it is realized by a program `P` of the machine
  `LinSysAmp.Supplement.OracleMachine` over `F₂ = ZMod 2` with the graph interface `graphIface O`
  (every call reads an `n × n` matrix, i.e. a graph with `n` vertices): on every input `A ∈ S_n` and
  every oracle, the output distribution of `P` after the step budget is that of Figure 6 (the
  output bit as a one-element list), every run makes exactly `t` calls, and every run halts with
  at most `C n² ε⁻² log(1/δ)` field operations. The input is `A` row-major and the index registers
  hold `n` and `t`. `P` and `C` are chosen before `n`, `ε`, `δ` and the oracle.
* `n ≥ 1` (§3.1); `log` is the natural logarithm.
* `ε ≤ 1/2` is added: the hypothesis `1/2 + ε ≤ Pr[O(A) = τ(A)]` already forces it; the cost
  clause holds for every oracle, and without it `ε⁻²` could be made arbitrarily small. -/
theorem theorem_5_8 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : OProgram (ZMod 2),
      ∀ n : ℕ, 1 ≤ n → ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ < 1 / 2 →
      ∀ O : Matrix (Fin n) (Fin n) (ZMod 2) → PMF (ZMod 2),
        let t : ℕ := ⌈1 / ε ^ 2 * Real.log (1 / δ)⌉₊
        let Bo : ℝ := C * (n : ℝ) ^ 2 / ε ^ 2 * Real.log (1 / δ)
        let N : ℕ := stepBudget t Bo
        (∀ A : GraphMat n,
          OHaltsWithin (graphIface O) P (oinit [(n : ℤ), (t : ℤ)] (flatMat A.1)) N t Bo ∧
          (∀ σ ∈ (orun (graphIface O) P N (oinit [(n : ℤ), (t : ℤ)] (flatMat A.1))).support,
            σ.calls = t) ∧
          (orun (graphIface O) P N (oinit [(n : ℤ), (t : ℤ)] (flatMat A.1))).map OConfig.status =
            (figure6 O t A.1).map fun b => OStatus.done (some (Out.vec [b]))) ∧
        (1 / 2 + ε ≤ triSuccess O →
          1 - δ ≤ (Fintype.card (GraphMat n) : ℝ)⁻¹ *
            ∑ A : GraphMat n, (figure6 O t A.1 (tau A.1)).toReal) := by sorry

end LinSysAmp.Supplement
