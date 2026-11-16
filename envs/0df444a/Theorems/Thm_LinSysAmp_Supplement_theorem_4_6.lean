-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_4_6
-- name    : LinSysAmp.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:49:21.076735+00:00
-- url     : https://prove2.me/theorems/e82b6f4b-5a0b-41d3-8c33-5e9d4957d594
-- title:
--   Theorem 4.6 — hardness self-amplification for LINEQ by a matrix walk (with the "Moreover" clause)
-- statement:
--   Let $\mathbb F_q$ be a finite field (every $q$, including $q=2$) and $n\ge1$. Let $O$ be an algorithm that solves $\mathrm{LINEQ}_{n,q}$ with probability at least $\alpha>0$, that is $\Pr_{M\leftarrow GL_n(\mathbb F_q),\,y\leftarrow\mathbb F_q^n,\,O}[O(M,y)=M^{-1}y]\ge\alpha$, and suppose each call to $O$ takes time $T$. For all $0<\beta,\delta<1/2$ there is an algorithm $B$, with oracle access to $O$, such that:
--
--   1. $B$ makes $O(\alpha^{-1}\log(1/(\beta\delta)))$ calls to $O$ and runs in time $$O\Big(\frac{T+n^2}{\alpha}\log\frac1{\beta\delta}\Big);$$
--   2. $B$ never outputs a wrong solution;
--   3. for all but a $\beta$ fraction of the matrices, $B$ succeeds with probability $1-\delta$ on every right-hand side: $$\Pr_{M\leftarrow GL_n(\mathbb F_q)}\Big[\forall y\in\mathbb F_q^n:\ \Pr_B[B(M,y)=M^{-1}y]\ge1-\delta\Big]\ge1-\beta.$$
--
--   Moreover, for every $0<\varepsilon<1/2$ there is an algorithm that runs in time $O((T+n^2)\alpha^{-1}\log(1/\varepsilon))$, never outputs a wrong solution, and fails with probability at most $\varepsilon$ on input $(M,y(M))$ with $M\leftarrow GL_n(\mathbb F_q)$, for every function $y$ of $M$.
--
--   The theorem turns a solver that works on a small fraction $\alpha$ of random systems into one that works on essentially every matrix and every right-hand side, at a cost of $O(\alpha^{-1})$ calls; it is the walk-based counterpart of the rank-$k$ Proposition 4.8.
--
--   **Formalization Note** Algorithms are programs of the published machine `LinSysAmp.Machine`, which reads a step count computed from $(\alpha,\beta,\delta)$ (the paper assumes $\alpha$ is known). The cost is stated as calls and field operations on every run, for every oracle and every invertible $M$; the fraction of matrices is a normalized count over $GL_n(\mathbb F_q)$.
--
--   Differences from the source:
--   - encoding: running time O((T + n²)/α · log(1/(βδ))) for a time-T oracle → on every run: calls ≤ C·α⁻¹·log(1/(βδ)), field operations ≤ C·n²·α⁻¹·log(1/(βδ)); reason: the oracle's cost T is charged per call, so the two bounds give the printed time bound; the machine counts calls and field operations separately
--   - reading: an O(·) bound with an unnamed constant and "there is an algorithm" → one absolute constant C, chosen before the field, and one program per field chosen before n, the parameters and the oracle; reason: the proof's constants are absolute and the reduction is black-box and uniform; this is the standard reading of O(·)
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed success probability α → they hold for every oracle; only the success guarantee assumes the success probability α; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: α unconstrained above → α ≤ 1 added; reason: a success probability is at most 1, so the hypothesis α ≤ Pr[success] already forces it; without it the unconditional cost bounds could not be met for large α
--   - reading: "runs in time O((T + n²)α⁻¹ log(1/ε))" and "fails with probability at most ε on (M, y) for y an arbitrary function of M" (Moreover clause) → calls ≤ C·α⁻¹·log(1/ε), operations ≤ C·n²·α⁻¹·log(1/ε); for every function y : GL_n → Fⁿ, the average over M of Pr[output = M⁻¹y(M)] is at least 1 − ε; reason: the time bound charges T per call; failure probability ε on a random M is average success 1 − ε
--   - reading: "The algorithm uses rank-one updates for q > 2 and rank-two updates for q = 2 (Remark 4.7)" → not stated; the program is existential; reason: the sentence describes how the algorithm is built, not a property of its output
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 4.6, pp.19–20 (PDF pp.21–22); Figure 2 and proof, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_LinSysAmp_Machine
import Definitions.Def_LinSysAmp_lineqSuccess

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u

/-- Theorem 4.6 (Hardness self-amplification for LINEQ), pp.19–20 (PDF pp.21–22). Couteau,
Melissaris, Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained
Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let O be a time-T algorithm that solves LINEQ_{n,q} with probability at least α > 0. For all
0 < β, δ < 1/2, there is an algorithm B with the following properties.
• B makes O(α⁻¹ log(1/(βδ))) calls to O, and runs in time O((T + n²)/α · log(1/(βδ))).
• B never outputs a wrong solution.
• For all but a β fraction of the matrices, B succeeds with probability 1 − δ on every right-hand
side: Pr_{M←GL_n(F_q)}[∀y ∈ F_qⁿ : Pr_B[B(M, y) = M⁻¹y] ≥ 1 − δ] ≥ 1 − β.
Moreover, for every 0 < ε < 1/2, there is an algorithm which runs in time
O((T + n²)α⁻¹ log(1/ε)), never outputs a wrong solution, and fails with probability at most ε on
input (M, y), where M ← GL_n(F_q) and y is an arbitrary function of M. The algorithm uses rank-one
updates for q > 2 and rank-two updates for q = 2, as explained in Remark 4.7."

**Formalization Note.**
* *Algorithm.* Each algorithm is a program of the published machine `LinSysAmp.Machine`, reached
  from the input layout `initConfig n 0 t M y`. The program is chosen for the field `F` only, before
  `n`, `α`, `β`, `δ` (resp. `ε`) and the oracle; the paper assumes that `α` is known (p.19), so the
  program reads a step count `t = tf α β δ` (resp. `tε α ε`) computed from the parameters alone.
  The same program works for every oracle (black-box reduction).
* *Constants.* One absolute constant `C`, chosen before the field (so uniform over every finite
  field, `q = 2` included), bounds every `O(·)`.
* *Time.* A time-`T` oracle enters only through the call counter. On every run (every configuration
  in the support, for every oracle and every invertible `M`) the program halts within the step
  budget with at most `C α⁻¹ log(1/(βδ))` calls and `C n² α⁻¹ log(1/(βδ))` field operations, so the
  total time is at most `C α⁻¹ log(1/(βδ))·(T + n²)`. In the "Moreover" clause the time bound
  `O((T + n²)α⁻¹ log(1/ε))` is read the same way (calls and operations separately).
* *Never wrong.* Every halted run with an output outputs `M⁻¹y`, for every oracle.
* *Success.* "Solves LINEQ with probability α" is `α ≤ lineqSuccess O`. The fraction of matrices is a
  normalized count over `InvMat n F`. "Fails with probability at most ε on (M, y(M))" is
  `1 − ε ≤ E_{M ← GL_n}[Pr[output = M⁻¹y(M)]]`, for every function `y : GL_n(F) → Fⁿ`.
* `n ≥ 1` (§3.1, "for an integer n ≥ 1"); `log` is the natural logarithm.
* `α ≤ 1` is added: a success probability is at most `1`, so the hypothesis `α ≤ lineqSuccess O`
  already forces it; the cost clauses hold for every oracle, and without it `α⁻¹` could be made
  arbitrarily small. -/
theorem theorem_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      (∃ P : LinSysAmp.Program F, ∃ tf : ℝ → ℝ → ℝ → ℕ,
        ∀ n : ℕ, 1 ≤ n → ∀ α β δ : ℝ, 0 < α → α ≤ 1 → 0 < β → β < 1 / 2 → 0 < δ → δ < 1 / 2 →
        ∀ O : LinSysAmp.Oracle n F,
          let t : ℕ := tf α β δ
          let Bc : ℝ := C / α * Real.log (1 / (β * δ))
          let Bo : ℝ := C * (n : ℝ) ^ 2 / α * Real.log (1 / (β * δ))
          let N : ℕ := ⌈Bc⌉₊ + ⌈Bo⌉₊ + 1
          (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
            LinSysAmp.HaltsWithin n O P (LinSysAmp.initConfig n 0 t M.1 y) N ⌊Bc⌋₊ Bo) ∧
          (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
            ∀ σ ∈ (LinSysAmp.run n O P N (LinSysAmp.initConfig n 0 t M.1 y)).support,
              ∀ w : Fin n → F, σ.status = .done (some w) → w = M.1⁻¹ *ᵥ y) ∧
          (α ≤ LinSysAmp.lineqSuccess O →
            1 - β ≤ ((Finset.univ.filter fun M : LinSysAmp.InvMat n F => ∀ y : Fin n → F,
                1 - δ ≤ LinSysAmp.outputProb n O P (LinSysAmp.initConfig n 0 t M.1 y) N
                  (M.1⁻¹ *ᵥ y)).card : ℝ) / (Fintype.card (LinSysAmp.InvMat n F) : ℝ))) ∧
      (∃ P : LinSysAmp.Program F, ∃ tε : ℝ → ℝ → ℕ,
        ∀ n : ℕ, 1 ≤ n → ∀ α ε : ℝ, 0 < α → α ≤ 1 → 0 < ε → ε < 1 / 2 →
        ∀ O : LinSysAmp.Oracle n F,
          let t : ℕ := tε α ε
          let Bc : ℝ := C / α * Real.log (1 / ε)
          let Bo : ℝ := C * (n : ℝ) ^ 2 / α * Real.log (1 / ε)
          let N : ℕ := ⌈Bc⌉₊ + ⌈Bo⌉₊ + 1
          (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
            LinSysAmp.HaltsWithin n O P (LinSysAmp.initConfig n 0 t M.1 y) N ⌊Bc⌋₊ Bo) ∧
          (∀ (M : LinSysAmp.InvMat n F) (y : Fin n → F),
            ∀ σ ∈ (LinSysAmp.run n O P N (LinSysAmp.initConfig n 0 t M.1 y)).support,
              ∀ w : Fin n → F, σ.status = .done (some w) → w = M.1⁻¹ *ᵥ y) ∧
          (α ≤ LinSysAmp.lineqSuccess O → ∀ y : LinSysAmp.InvMat n F → (Fin n → F),
            1 - ε ≤ (Fintype.card (LinSysAmp.InvMat n F) : ℝ)⁻¹ *
              ∑ M : LinSysAmp.InvMat n F,
                LinSysAmp.outputProb n O P (LinSysAmp.initConfig n 0 t M.1 (y M)) N
                  (M.1⁻¹ *ᵥ y M))) := by sorry

end LinSysAmp.Supplement
