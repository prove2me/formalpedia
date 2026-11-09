-- Prove2me | Theorems.Thm_LinfContractionFP_theorem_1
-- name    : LinfContractionFP.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:16.959199+00:00
-- url     : https://prove2.me/theorems/ac20846e-3420-4898-817e-37b455941b1e
-- title:
--   Theorem 1 — an $\varepsilon$-near fixed point in $(\log\frac1{\gamma\varepsilon})^{C\log^2 d}$ steps
-- statement:
--   There are one fixed program $P$ of the unit-cost real RAM with an oracle for $f$, using only rational constants, and one universal constant $C$ such that the following holds. For every $d\ge2$, every contraction gap $\gamma\in(0,1]$, every nearness tolerance $0<\varepsilon\le1/4$ and every $(1-\gamma)$-contraction $f:[0,1]^d\to[0,1]^d$ in the $\ell_\infty$ norm, $P$, given $d,\gamma,\varepsilon$ and oracle access to $f$, halts within
--   $$\Big(\log\frac1{\gamma\varepsilon}\Big)^{C\log^2d}$$
--   steps, every arithmetic operation, comparison, memory or control instruction and evaluation of $f$ counting as one step, and outputs an $\varepsilon$-near fixed point of $f$.
--
--   This is the paper's main result: the first quasipolynomial-time algorithm for near fixed points of $\ell_\infty$-contractions.
--
--   Differences from the source:
--   - reading: the total number of arithmetic operations and exact evaluations of f performed by Solve(f, ε) → ∃ one admissible program P of the real RAM with an f-query instruction, chosen before C, d, γ, ε and f, whose step count is bounded; reason: Solve is the witness; Corollary 1 (p.2) phrases the result as 'there exists a deterministic algorithm'
--   - reading: arithmetic operations, comparisons and evaluations of f are counted → every executed instruction is one step, including loads, stores, pointer operations and jumps; reason: counting more steps makes the bound at least as strong
--   - reading: unit-cost real machine (footnote 6) → only rational machine constants (Admissible); reason: excludes advice hidden in an irrational constant; a stronger existence claim
--   - encoding: f : [0,1]^d → [0,1]^d; inputs f, ε (γ used by Algorithms 2, 4) → f total with arbitrary values off the cube; d, γ, ε in memory cells 0–2; output in cells 3, …, d+2; reason: the program must clip, as the paper's extension does
--   - reading: log and log² d in (1) → natural logarithm; (log d)²; reason: base changes are absorbed by C since log(1/(γε)) ≥ log 4 > 1
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Theorem 1, p.2 (restated p.21)

import Mathlib
import Definitions.Def_LinfContractionFP_Admissible
import Definitions.Def_LinfContractionFP_RunsWithin
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_IsNearFixed

namespace LinfContractionFP

/-- Theorem 1: one fixed program of the unit-cost real RAM with an oracle for `f` and one universal
constant `C` such that, for every `d ≥ 2`, every `γ ∈ (0, 1]`, every `ε ∈ (0, 1/4]` and every
`(1 − γ)`-contraction `f` of `[0,1]^d` in the ℓ∞ norm, the program, given `d, γ, ε` and oracle
access to `f`, halts within `(log(1/(γε)))^{C log² d}` steps with an `ε`-near fixed point of `f`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Theorem 1, p.2 (restated p.21): "Theorem 1. Fix d ≥ 2, a contraction gap γ ∈ (0, 1], and a
desired nearness tolerance 0 < ε ≤ 1/4. For a (1 − γ)-contraction f : [0, 1]^d → [0, 1]^d, the
total number of arithmetic operations and exact evaluations of f performed by Solve(f, ε) to
return an ε-near fixed point of f is upper bounded by (log 1/(γε))^{C log² d}, (1) for a
universal constant C."

**Formalization Note.**
* "Solve(f, ε) performs at most …" is stated as the existence of one admissible program `P`
  (rational constants only), chosen before `C`, `d`, `γ`, `ε` and `f`; Solve is its witness
  (Corollary 1, p.2, phrases the result as "there exists a deterministic algorithm"). The
  machine has no coins, so the program is deterministic.
* Every executed instruction is a step: arithmetic, comparisons, loads, stores, pointer
  operations, jumps and oracle queries (one step each). The paper counts arithmetic operations,
  comparisons and evaluations of `f`; counting more makes the bound at least as strong.
* `γ`, `d`, `ε` are inputs of the program (`inputMem`); Algorithms 2 and 4 use `γ`. `f`'s values
  off `[0,1]^d` are arbitrary, so the program must clip, as the paper's extension does.
* `log` is the natural logarithm and `log² d = (log d)²` (`Real.log d ^ 2`); the power is
  `Real.rpow` with base `log(1/(γε)) ≥ log 4 > 1`. -/
theorem theorem_1 : ∃ P : Program, Admissible P ∧ ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      ∀ f : (Fin d → ℝ) → (Fin d → ℝ), IsContraction γ f →
        ∃ T : ℕ, (T : ℝ) ≤ Real.log (1 / (γ * ε)) ^ (C * Real.log d ^ 2) ∧
          ∃ x : Fin d → ℝ, RunsWithin P d f γ ε T x ∧ IsNearFixed f ε x := by sorry

end LinfContractionFP
