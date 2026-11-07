-- Prove2me | Theorems.Thm_MatrixSpencer_theorem_1_3
-- name    : MatrixSpencer.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:39.417046+00:00
-- url     : https://prove2.me/theorems/1f9b53b7-6eb9-49f1-b8f8-af13be5461c3
-- title:
--   Theorem 1.3, p.1 — Matrix Spencer: a universal $C$ with $\min_x\|\sum x_iA_i\|\le C\sqrt n\sqrt{\max\{1,\log(d/n)\}}$, and a coloring found in randomized polynomial time
-- statement:
--   There is a universal constant $C>0$ with the following two properties.
--
--   1. For all $n,d$ and all symmetric $A_1,\dots,A_n\in\mathbb R^{d\times d}$ with $\|A_i\|\le1$ in the operator norm,
--   $$\min_{x\in\{\pm1\}^n}\Bigl\|\sum_{i=1}^nx_iA_i\Bigr\|\le C\sqrt n\,\sqrt{\max\{1,\log(d/n)\}}.$$
--   2. There are a polynomial-time Turing machine and a fixed $k$ such that for all $n,d$ and all rational symmetric $A_1,\dots,A_n$ with $\|A_i\|\le1$, on at least a $2/3$ fraction of the coin strings of length $|\mathrm{enc}(I)|^k+k$, the machine outputs a coloring within this bound.
--
--   This resolves the Matrix Spencer conjecture, the extension of Spencer's "six standard deviations suffice" to symmetric matrices, in which a random coloring loses a factor $\sqrt{\log d}$.
--
--   **Formalization Note** $C$ and the machine are chosen before $n$, $d$ and the matrices. The input has rational entries in binary and $n,d$ in unary. The machine gets fair coins as an explicit second input, so its time bound holds on every coin string.
--
--   Differences from the source:
--   - reading: "can be found efficiently", and in the proof, "randomized polynomial-time" (no machine, input format or success probability printed) → one Mathlib TM2 machine in polynomial time, chosen before the instance; rational entries in binary, n and d in unary; fair coins as a second input of length |enc I|^k + k with k fixed, so time is bounded on every coin string; correct on at least 2/3 of the coin strings; reason: the paper names no model; a Turing machine reads finite strings, so inputs are rational. Candidate outputs can be checked to a constant factor in polynomial time, so 2/3 amplifies at the cost of the constant
--   - encoding: min over x ∈ {±1}ⁿ → ∃ x with x i = 1 or −1 below the bound; reason: a finite nonempty minimum is below the bound exactly when some element is
--   - encoding: constant C in the first clause and O(·) in the second → one C for both; reason: the bound is monotone in C, so the larger of two constants serves both
--   - encoding: n and d unrestricted, unprinted at 0 → n = 0 and d = 0 are included, with Lean's log 0 = 0 and d/0 = 0; reason: the statement is then true and trivial: the matrix sum is 0 or empty
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.3, p.1 (PDF p.3); randomized polynomial time, proof of Theorem 1.3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MatrixSpencer_MatInst
import Definitions.Def_MatrixSpencer_encMatInst
import Definitions.Def_MatrixSpencer_encMatInstCoins
import Definitions.Def_MatrixSpencer_Good
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer

/-- **Theorem 1.3 (Matrix Spencer).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.3, p.1 (PDF p.3): "There exists a universal constant C > 0 such that for every family
of symmetric d × d matrices A₁, …, Aₙ with ‖Aᵢ‖ ≤ 1, min_{x∈{±1}ⁿ} ‖∑ⁿᵢ₌₁ xᵢAᵢ‖ ≤ C√n · √(max{1,
log(d/n)}). Moreover, a coloring with discrepancy at most O(√n · √(max{1, log(d/n)})) can be found
efficiently."

**Formalization Note.** `‖·‖` is the operator norm. One `C` serves both clauses (the bound is monotone
in `C`, so this is the same as two constants). `C` and the machine are chosen before `n`, `d` and the
matrices. The minimum over the finite nonempty set `{±1}ⁿ` is an `∃`.

"Found efficiently" is read in the bit model (the paper's own phrase, p.12, is "randomized polynomial
time"; it names no machine): one `Turing.TM2ComputableInPolyTime` machine, on rational entries in
binary and `n`, `d` in unary. It receives fair coins as a second input of length `|enc I|^k + k`, so its
time bound holds on every coin string. It is correct on at least a 2/3 fraction of coin strings; a
candidate coloring can be checked to a constant factor in polynomial time, so 2/3 amplifies, at the
cost of the constant. `n` and `d` may be `0`: then `log(d/n)` is Lean's `log 0 = 0`, both sides are `0`
or the empty sum, and the statement is true. -/
theorem theorem_1_3 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n d : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ),
        (∀ i, (A i).IsSymm) → (∀ i, ‖A i‖ ≤ 1) →
          ∃ x : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) ∧
            ‖∑ i, x i • A i‖ ≤ C * √(n : ℝ) * √(max 1 (Real.log ((d : ℝ) / n)))) ∧
      ∃ (alg : MatInst × List Bool → List Bool) (k : ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encMatInstCoins (fun m : List Bool => m) alg) ∧
        ∀ I : MatInst, (∀ i, (I.A i).IsSymm) →
          (∀ i, ‖(I.A i).map (fun q : ℚ => (q : ℝ))‖ ≤ 1) →
            open Classical in
            2 * 2 ^ ((encMatInst I).length ^ k + k) ≤
              3 * (Finset.univ.filter fun c : Fin ((encMatInst I).length ^ k + k) → Bool =>
                Good C I (alg (I, List.ofFn c))).card := by sorry

end MatrixSpencer
