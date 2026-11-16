-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_Supplement_theorem_2
-- name    : HypercliqueCircuits.Circuits.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:12:31.385208+00:00
-- url     : https://prove2.me/theorems/014d3383-414f-4a0d-85cf-d4b2aa8fad16
-- title:
--   Theorem 2 — exact hyperclique counting
-- statement:
--   Fix $k\ge3$, and let $\varepsilon_k=\operatorname{saving}(k)$ be the published saving of Theorem 1. There is one algorithm which, on every $(k-1)$-uniform hypergraph $H$ on $n\ge1$ vertices, outputs its number of unordered $k$-hypercliques. For every real $\eta>0$, there is a constant $C_{k,\eta}>0$ such that its bit cost satisfies
--
--   $$T(H)\le C_{k,\eta}n^{k-\varepsilon_k+\eta}.$$
--
--   The algorithm is chosen before $\eta$ and works for all input sizes and hypergraphs. Its output is one natural word containing the exact count. This is the full counting application of the circuit result, rather than detection or the count of ordered tuples.
--
--   Differences from the source:
--   - reading: algorithmic running time without an explicit instruction set → a finite Program Empty with actual halting execution and the published executionBits cost; reason: the supplement inherits the live mission machine; arithmetic, accessed-word lengths, and output serialization are charged, and no oracle instruction can be instantiated
--   - encoding: a hypergraph on n vertices and its number of k-hypercliques → the published Fin n hypergraph with its dense (k-1)-tuple indicator and one output word counting k-element vertex sets; reason: zero-based labels and dense indicators represent every finite input; counting sets retains the source factor of k! between the answer and polynomial evaluation
--   - encoding: n^(k−ε_k+o(1)) with ε_k from Theorem 1 → saving k and a program chosen before every η>0, with a constant C depending only on k and η; reason: this is the uniform asymptotic upper-bound meaning of o(1), with no replacement of the published saving
--   - encoding: asymptotic running time in the input size → an explicit positive multiplicative constant and a bound for every n at least 1; reason: finitely many smaller positive sizes are absorbed into the constant; n=0 is outside the power-bound convention
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, p.2, Theorem 2 (PDF 3); proof p.24 (PDF 25)

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Counting

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- Theorem 2, printed p.2 (proof p.24), PDF p.3 (proof p.25).
The SAME program works for every positive asymptotic slack. -/
theorem theorem_2 (k : ℕ) (hk : 3 ≤ k) :
    ∃ prog : Program Empty, ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
        ∀ H : HypercliqueFalse.Hypergraph n (k - 1), ∃ t : ℕ,
          (execute prog (countingInput H) t).halted = true ∧
          (execute prog (countingInput H) t).output = words [cliqueCount H k] ∧
          (executionBits Empty.elim prog (countingInput H) t : ℝ) ≤
            C * (n : ℝ) ^ ((k : ℝ) - saving k + η) := by sorry

end HypercliqueCircuits.Circuits.Supplement
