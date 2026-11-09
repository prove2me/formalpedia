-- Prove2me | Theorems.Thm_OracleStateHSP_proposition_4_6
-- name    : OracleStateHSP.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:57.486838+00:00
-- url     : https://prove2.me/theorems/980b718f-7ffc-4250-8da8-04bef13e87c2
-- title:
--   Proposition 4.6 (Simon's decision lower bound [KNP05, Theorem 1])
-- statement:
--   There is a universal constant $c > 0$ such that the following holds for every $m \ge 1$. Let $A$ be a $T$-query algorithm of Definition 4.1 whose oracle is Simon's oracle $O_f|x\rangle|b\rangle = |x\rangle|b + f(x)\rangle$ on $\mathbb Z_2^m \times \mathbb Z_2^m$, with a fixed initial state and output map into $\{\text{bijective}, \text{periodic}\}$. If $A$ outputs "bijective" with probability at least $2/3$ for every bijection $f$, and "periodic" with probability at least $2/3$ for every $f$ that hides a nonzero period, then
--   $$
--   T \ge c\, m .
--   $$
--
--   That is, deciding whether $f$ is a bijection or hides a nonzero period requires $\Omega(m)$ queries. The paper cites this result (Koiran, Nesme and Portier, ICALP 2005, Theorem 1) and does not prove it; it is the base of the whole lower-bound chain.
--
--   **Formalization Note** "Bijective" is the output `true`, "periodic" the output `false`.
--
--   Differences from the source:
--   - generalization: queries to O_f (forward) → the model of Definition 4.1: forward and inverse queries, with controlled queries through the direct sum S ⊕ (H_S ⊗ W); reason: p.37 states the bound in this model (O_f is self-inverse and controlled-O_f costs one query); the forward-only bound is the special case
--   - reading: Ω(m) queries → one constant c > 0 chosen before m with c·m ≤ T for all m ≥ 1; reason: for every m ≥ 1 at least one query is needed (a 0-query algorithm has one output distribution and cannot satisfy both classes), so the uniform bound is equivalent to the asymptotic one
--   - encoding: measuring a designated output register → a whole-register computational-basis measurement followed by an output map out; reason: a register measurement is such a map, and out(z) can be written into an output register by one final permutation unitary
--   - encoding: finite-dimensional spaces S and W → S = Fin a, W = Fin b for arbitrary a, b; reason: only the dimensions of S and W matter
--   - encoding: f ranges over Simon functions with nonzero period s(f) → x ranges over pairs (f, s) with f hiding s and s ≠ 0; reason: a nonzero period is unique, so the pairs are in bijection with the functions
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Proposition 4.6, p.36 (cited: [KNP05, Theorem 1]); p.37 (inverse and controlled oracles)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb
import Definitions.Def_OracleStateHSP_SimonInst

namespace OracleStateHSP

/-- Proposition 4.6 of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.36 (Simon's decision lower bound, cited there from Koiran, Nesme
and Portier [KNP05, Theorem 1] and not proved in the paper): any quantum algorithm that uses
queries to `O_f` to decide whether `f : Z_2^m → Z_2^m` is a bijection or hides a nonzero period,
with success probability at least `2/3`, requires `Ω(m)` queries.

Here: there is a universal `c > 0` such that for every `m ≥ 1`, every `T`-query algorithm of
Definition 4.1 with oracle `O_f` (the XOR oracle on `Z_2^m × Z_2^m`) that outputs `true` with
probability `≥ 2/3` on every bijective `f` and `false` with probability `≥ 2/3` on every `f` with a
nonzero period uses `T ≥ c m` queries.

**Formalization Note.** `Ω(m)` is one constant `c > 0` chosen before `m`. The model of
Definition 4.1 also allows inverse queries and, through the direct sum, controlled queries; p.37
notes that the bound holds there (`O_f` is self-inverse, and controlled-`O_f` costs one query).
The output is a whole-register measurement followed by `out`. -/
theorem proposition_4_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ (T a b : ℕ) (A : QueryAlgorithm (V m × V m) (Fin a) (Fin b) T), A.IsDef41 →
      ∀ (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ ((V m × V m) × Fin b)))
        (out : Fin a ⊕ ((V m × V m) × Fin b) → Bool), ‖ψ₀‖ = 1 →
        (∀ f : V m → V m, Function.Bijective f →
          (2 : ℝ) / 3 ≤ A.outputProb (QAlgorithms.xorOracle f) ψ₀ out true) →
        (∀ x : SimonInst m, (2 : ℝ) / 3 ≤ A.outputProb (QAlgorithms.xorOracle x.fn) ψ₀ out false) →
        c * m ≤ T := by sorry

end OracleStateHSP
