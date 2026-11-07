-- Prove2me | Theorems.Thm_MatrixSpencer_theorem_2_7
-- name    : MatrixSpencer.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:17.991107+00:00
-- url     : https://prove2.me/theorems/0d284cfd-dbe2-4470-88d4-98c15eab3e4b
-- title:
--   Theorem 2.7, p.11 — main partial-coloring theorem, with a randomized polynomial-time algorithm
-- statement:
--   There is a universal constant $C>0$ with the following two properties.
--
--   1. Let $A_1,\dots,A_n\in\mathbb R^{d\times d}$ be symmetric with $\|\sum_iA_i^2\|\le\sigma^2$ for some $\sigma\ge0$. Then for every $x^{(0)}\in(-1,1)^n$ there is $x\in[-1,1]^n$ with $|\{i:|x_i|=1\}|\ge n/2$ and
--   $$\Bigl\|\sum_{i=1}^n(x_i-x_i^{(0)})A_i\Bigr\|\le C\sigma\sqrt{\max\{1,\log(d/n)\}}.$$
--   2. There are a polynomial-time Turing machine and a fixed $k$ such that for all rational symmetric $A_i$ and rational $x^{(0)}\in(-1,1)^n$, on at least a $2/3$ fraction of the coin strings of length $|\mathrm{enc}(I)|^k+k$, the machine outputs a rational $x$ as in item 1, with $\sigma=\sqrt{\|\sum_iA_i^2\|}$.
--
--   This is the step that is iterated to prove the main theorem.
--
--   **Formalization Note** Item 2 takes no $\sigma$. Meeting the bound for the smallest admissible $\sigma$ implies it for every admissible $\sigma$.
--
--   Differences from the source:
--   - reading: "such an x can be found by a randomized polynomial-time algorithm": "randomized polynomial-time" (no machine, input format or success probability printed) → one Mathlib TM2 machine in polynomial time, chosen before the instance; rational entries in binary, n and d in unary; fair coins as a second input of length |enc I|^k + k with k fixed, so time is bounded on every coin string; correct on at least 2/3 of the coin strings; reason: the paper names no model; a Turing machine reads finite strings, so inputs are rational. Candidate outputs can be checked to a constant factor in polynomial time, so 2/3 amplifies at the cost of the constant
--   - reading: the algorithm is given σ → the algorithm takes no σ and meets the bound for σ = √‖ΣAᵢ²‖; reason: the smallest admissible σ implies the printed bound for every σ
--   - encoding: x⁽⁰⁾ ∈ (−1, 1)ⁿ real, for both clauses → x⁽⁰⁾ rational in the algorithmic clause, real in the existence clause; reason: the machine reads finite strings; the existence clause keeps the full real domain
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_MatrixSpencer_PartialInst
import Definitions.Def_MatrixSpencer_encPartialInst
import Definitions.Def_MatrixSpencer_encPartialInstCoins
import Definitions.Def_RobustToDynamics_encListRat
import Definitions.Def_MatrixSpencer_GoodPartial
open scoped Matrix.Norms.L2Operator

namespace MatrixSpencer

/-- **Theorem 2.7 (Main partial-coloring theorem).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11 (PDF p.13): "There exists a universal constant C > 0 with the following property.
Let A₁, …, Aₙ ∈ ℝ^{d×d} be symmetric matrices and suppose that ‖∑ⁿᵢ₌₁ Aᵢ²‖ ≤ σ² for some σ ≥ 0. Then,
for every x⁽⁰⁾ ∈ (−1, 1)ⁿ, there exists x ∈ [−1, 1]ⁿ such that |{i ∈ [n] : |xᵢ| = 1}| ≥ n/2 and
‖∑ⁿᵢ₌₁ (xᵢ − xᵢ⁽⁰⁾)Aᵢ‖ ≤ Cσ√(max{1, log(d/n)}). (2.12) Moreover, such an x can be found by a randomized
polynomial-time algorithm."

**Formalization Note.** One `C` serves both clauses. The existence clause is over all real matrices and
all admissible `σ`. The algorithmic clause is read as in `theorem_1_3`: one machine, rational binary
entries, unary `n` and `d`, fair coins of length `|enc I|^k + k`, correct on at least a 2/3 fraction of
coin strings, a list of rationals as output. It takes no `σ` and meets the bound for the smallest
admissible one, `√‖∑ᵢAᵢ²‖`, which implies the bound for every `σ`. -/
theorem theorem_2_7 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n d : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ) (σ : ℝ),
        (∀ i, (A i).IsSymm) → 0 ≤ σ → ‖∑ i, A i ^ 2‖ ≤ σ ^ 2 →
        ∀ x0 : Fin n → ℝ, (∀ i, |x0 i| < 1) →
          open Classical in
          ∃ x : Fin n → ℝ, (∀ i, |x i| ≤ 1) ∧
            (n : ℝ) / 2 ≤ ((Finset.univ.filter fun i => |x i| = 1).card : ℝ) ∧
            ‖∑ i, (x i - x0 i) • A i‖ ≤ C * σ * √(max 1 (Real.log ((d : ℝ) / n)))) ∧
      ∃ (alg : PartialInst × List Bool → List ℚ) (k : ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encPartialInstCoins RobustToDynamics.encListRat alg) ∧
        ∀ I : PartialInst, (∀ i, (I.inst.A i).IsSymm) → (∀ i, |I.x0 i| < 1) →
          open Classical in
          2 * 2 ^ ((encPartialInst I).length ^ k + k) ≤
            3 * (Finset.univ.filter fun c : Fin ((encPartialInst I).length ^ k + k) → Bool =>
              GoodPartial C I (alg (I, List.ofFn c))).card := by sorry

end MatrixSpencer
