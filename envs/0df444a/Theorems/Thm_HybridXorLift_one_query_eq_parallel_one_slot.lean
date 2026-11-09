-- Prove2me | Theorems.Thm_HybridXorLift_one_query_eq_parallel_one_slot
-- name    : HybridXorLift.one_query_eq_parallel_one_slot
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:03.205834+00:00
-- url     : https://prove2.me/theorems/15ab9880-661c-4419-a81e-235da866e2e2
-- title:
--   §2.2 — one-query hybrid algorithms are exactly the parallel one-slot hybrid algorithms
-- statement:
--   A subroutine with a single query is parallel with one slot. Hence one-query hybrid algorithms are exactly the parallel $1$-query hybrid algorithms:
--
--   1. for every one-query hybrid algorithm $A$ there is a parallel $1$-query hybrid algorithm $B$ with the same cost and the same output probabilities $\Pr[B(x) = a] = \Pr[A(x) = a]$ for every input $x$ and output $a$;
--   2. conversely, for a nonempty index set, every parallel $1$-query hybrid algorithm has a one-query hybrid algorithm with the same cost and the same output probabilities.
--
--   This is the bridge by which Theorem 1.1 is the case $q = 1$ of Theorem 1.5.
--
--   **Formalization Note** The converse needs a nonempty index set only because of the register type of the encoding: a sequential subroutine's register $(\iota \times \{0,1\}) \times [w]$ is empty when $\iota$ is, while a parallel subroutine with zero slots still has a nonempty register.
--
--   Differences from the source:
--   - encoding: a subroutine starts from an input-independent (possibly mixed) state and ends with an arbitrary measurement → a pure unit start state on query register(s) × workspace Fin w, input-independent unitaries, and a complete computational-basis measurement with one child per outcome; reason: §2.2: purifying every preparation and dilating every measurement change neither the cost nor the output distribution, so the class of algorithms is the paper's
--   - encoding: the identification for every input index set → the converse direction under [Nonempty ι]; reason: with ι empty the sequential register (ι × Bool) × Fin w is empty and carries no unit state, while a zero-slot parallel subroutine does; nothing changes for the physical index sets Fin n × Fin r with n, r ≥ 1
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.2, p.10 (PDF p.12)

import Definitions.Def_HybridXorLift_HybridAlg_outProb
import Definitions.Def_HybridXorLift_HybridAlg_cost
import Definitions.Def_HybridXorLift_HybridAlg_RoundsAtMost
import Definitions.Def_HybridXorLift_ParallelHybridAlg_outProb
import Definitions.Def_HybridXorLift_ParallelHybridAlg_cost
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- §2.2 of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.10 (PDF p.12): "A subroutine with a single query is parallel with one slot.
Hence one-query hybrid algorithms are exactly the parallel 1-query hybrid algorithms." Every
one-query hybrid algorithm has a parallel one-slot hybrid algorithm with the same cost and the
same output probabilities on every input, and conversely.

**Formalization Note** The converse is stated for a nonempty index type: when `ι` is empty a
sequential subroutine's register `(ι × Bool) × Fin w` is empty and carries no unit state, while a
parallel subroutine with zero slots still has the register `(Fin 0 → ι × Bool) × Fin w`. -/
theorem one_query_eq_parallel_one_slot {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type}
    [DecidableEq α] :
    (∀ A : HybridAlg ι α, A.RoundsAtMost 1 →
      ∃ B : ParallelHybridAlg ι α, B.SlotsAtMost 1 ∧ B.cost = A.cost ∧ B.outProb = A.outProb) ∧
    ([Nonempty ι] → ∀ B : ParallelHybridAlg ι α, B.SlotsAtMost 1 →
      ∃ A : HybridAlg ι α, A.RoundsAtMost 1 ∧ A.cost = B.cost ∧ A.outProb = B.outProb) := by sorry

end HybridXorLift
