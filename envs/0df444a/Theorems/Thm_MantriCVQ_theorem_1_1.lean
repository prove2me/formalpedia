-- Prove2me | Theorems.Thm_MantriCVQ_theorem_1_1
-- name    : MantriCVQ.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:27.136841+00:00
-- url     : https://prove2.me/theorems/9c9adc43-07c8-48ad-9225-bffb6d8da686
-- title:
--   Theorem 1.1 — a unary language in $\mathsf{EQP}^O\setminus\mathsf{PH}^O$ with a public-coin classical proof, an efficient quantum prover, soundness $1/4$ and at most $\log n/4$ messages
-- statement:
--   There are a classical Boolean oracle $O$ and a total unary language $L\subseteq\{1^n:n\in\mathbb N\}$ such that
--   $$L\in\mathsf{EQP}^O\quad\text{and}\quad L\notin\mathsf{PH}^O,$$
--   and $L$ has an interactive proof system relative to $O$ with a classical polynomial-time verifier, an efficient quantum honest prover, perfect completeness, and soundness error at most $1/4$ against computationally unbounded provers. The proof system is public-coin and uses at most $\log_2n/4$ messages on input $1^n$.
--
--   The soundness clause quantifies over all prover strategies. The message count is the number of communication slots, with empty slots included. The goal thus gives a language decided exactly by a quantum computer, outside the polynomial hierarchy relative to the oracle, whose membership a classical verifier can still check with a quantum prover's help.
--
--   Differences from the source:
--   - generalization: a fixed finite inverse-closed gate set containing H, NOT and Toffoli → the gate set {H, X, Toffoli} for the circuits and the honest prover; reason: it is contained in every admissible gate set, so the Lean statement implies the paper's for every choice
--   - encoding: a query maps |a⟩|b⟩ to |a⟩|b + O(a)⟩ → an oracle gate on a list of address wires and one answer wire outside it; reason: the same action
--   - encoding: a uniform family of polynomial-size circuits → a polynomial-time map with no oracle from 1^n to the description, one polynomial bounding size and ancillas; reason: the standard meaning
--   - reading: V a deterministic polynomial-time oracle machine, PH^O the union of all the classes → V halts within a polynomial clock on every input for this O only; the union over k ≥ 0 of Sigma and Pi; reason: this enlarges PH^O, so L ∉ PH^O is the stronger statement; §7.1's diagonalization clocks every machine
--   - encoding: a public-coin proof in the fixed-schedule form, every slot a message → PCVerifier: an oracle-free polynomial-time schedule, uniform verifier slots and a clocked decision machine; the message count is the slot count; reason: §3.1's definition; the schedule is fixed, so the maximum over provers and coins is the slot count
--   - generalization: every prover, classical or quantum, that communicates classically → every map from the input and transcript to a distribution on the next message; reason: such a prover induces these conditional laws; the class of strategies contains all of them
--   - reading: an efficient honest prover: a uniform polynomial-time quantum algorithm with query access to O → a memoryless uniform polynomial-size circuit family over {H, X, Toffoli}, measured per slot; reason: a special case, so its existence is stronger; the paper's prover recomputes every secret afresh
--   - encoding: at most log n/4 messages on input 1^n; a total unary language → S(1^n) ≤ logb 2 n / 4 for every n ≥ 1; L a subset of the range of unary; reason: the paper's logarithms are base two, and there is no promise
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.1, pp. 2–3 (PDF pp. 4–5)

import Mathlib
import Definitions.Def_MantriCVQ_EQP
import Definitions.Def_MantriCVQ_PH
import Definitions.Def_MantriCVQ_HasPCProof

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- **Theorem 1.1** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.1, pp. 2–3
(PDF pp. 4–5)): there are a classical Boolean oracle `O` and a total unary language `L` with
`L ∈ EQP^O` and `L ∉ PH^O`, and `L` has a public-coin proof system relative to `O` with a classical
polynomial-time verifier, an efficient quantum honest prover, perfect completeness, soundness error
at most `1/4` against every prover, and at most `log n / 4` messages on input `1^n`.

**Formalization Note** The gate set is `{H, X, Toffoli}`, the smallest admissible one (§3.1), so the
statement implies the paper's for every admissible gate set. `PH O` allows machines polynomial-time for
this `O` only, which makes `L ∉ PH O` stronger. A prover in soundness is any behavioural strategy. The
message count is the slot count, empty slots included. `log` is `log₂`, for `n ≥ 1`. -/
theorem theorem_1_1 : ∃ (O : Oracle) (L : Set Str),
    L ⊆ Set.range unary ∧ L ∈ EQP G0 O ∧ L ∉ PH O ∧
      ∃ V : PCVerifier, HasPCProof O L V := by sorry

end MantriCVQ
