-- Prove2me | Theorems.Thm_OracleStateHSP_proposition_4_7
-- name    : OracleStateHSP.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:30.884387+00:00
-- url     : https://prove2.me/theorems/daac5444-bd12-46d2-8fad-b3cfe33eb945
-- title:
--   Proposition 4.7 (Simon's search lower bound)
-- statement:
--   There is a universal constant $c > 0$ such that the following holds for every $m \ge 2$. Let $A$ be a $T$-query algorithm of Definition 4.1 with oracle $O_f$ on $\mathbb Z_2^m \times \mathbb Z_2^m$, a fixed initial state and an output map into $\mathbb Z_2^m$. If, for every $f : \mathbb Z_2^m \to \mathbb Z_2^m$ hiding a nonzero period $s(f)$, $A$ outputs $s(f)$ with probability at least $2/3$, then
--   $$
--   T \ge c\, m .
--   $$
--   The behaviour of $A$ on functions outside the promise is unconstrained.
--
--   This search version is the step from the decision bound of Proposition 4.6 to hidden-subgroup recovery.
--
--   Differences from the source:
--   - generalization: queries to O_f (forward) → the model of Definition 4.1: forward and inverse queries, with controlled queries through the direct sum S ⊕ (H_S ⊗ W); reason: p.37 states the bound in this model (O_f is self-inverse and controlled-O_f costs one query); the forward-only bound is the special case
--   - reading: Ω(m) queries, f : Z_2^m → Z_2^m → one constant c > 0 chosen before m with c·m ≤ T for all m ≥ 2; reason: at m = 1 the only nonzero period is 1, which a 0-query algorithm outputs, so a uniform linear bound needs m ≥ 2; for m ≥ 2 there are at least three possible periods, every successful algorithm makes a query, and the uniform bound is equivalent to the asymptotic one
--   - encoding: outputs in Z_2^m or a symbol indicating that the promise fails → outputs in Z_2^m; reason: the symbol is never a correct answer on promise inputs and can be mapped to 0
--   - encoding: measuring a designated output register → a whole-register computational-basis measurement followed by an output map out; reason: a register measurement is such a map, and out(z) can be written into an output register by one final permutation unitary
--   - encoding: finite-dimensional spaces S and W → S = Fin a, W = Fin b for arbitrary a, b; reason: only the dimensions of S and W matter
--   - encoding: f ranges over Simon functions with nonzero period s(f) → x ranges over pairs (f, s) with f hiding s and s ≠ 0; reason: a nonzero period is unique, so the pairs are in bijection with the functions
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Proposition 4.7, p.37

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb
import Definitions.Def_OracleStateHSP_SimonInst

namespace OracleStateHSP

/-- Proposition 4.7 of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.37 (Simon's search lower bound): let `f : Z_2^m → Z_2^m` hide a
nonzero period `s(f)`; any quantum algorithm that queries `O_f` to determine `s(f)`, with success
probability at least `2/3`, requires `Ω(m)` queries.

Here: there is a universal `c > 0` such that for every `m ≥ 2`, every `T`-query algorithm of
Definition 4.1 with oracle `O_f` that outputs `s(f)` with probability `≥ 2/3` for every `f` with a
nonzero period uses `T ≥ c m` queries. Its behaviour on other `f` is unconstrained.

**Formalization Note.** `Ω(m)` is one constant `c > 0` chosen before `m`, on `m ≥ 2`: at `m = 1`
the only nonzero period is `1`, which a 0-query algorithm outputs, so the uniform form needs
`m ≥ 2`; on `m ≥ 2` it is equivalent to the asymptotic `Ω(m)` (there are at least three possible
periods, so every successful algorithm makes a query). Inverse and controlled queries are allowed
(Definition 4.1; p.37). The answer set is `Z_2^m` (a "promise fails" symbol is never a correct
answer and can be mapped to `0`). -/
theorem proposition_4_7 :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m →
      ∀ (T a b : ℕ) (A : QueryAlgorithm (V m × V m) (Fin a) (Fin b) T), A.IsDef41 →
      ∀ (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ ((V m × V m) × Fin b)))
        (out : Fin a ⊕ ((V m × V m) × Fin b) → V m), ‖ψ₀‖ = 1 →
        (∀ x : SimonInst m,
          (2 : ℝ) / 3 ≤ A.outputProb (QAlgorithms.xorOracle x.fn) ψ₀ out x.period) →
        c * m ≤ T := by sorry

end OracleStateHSP
