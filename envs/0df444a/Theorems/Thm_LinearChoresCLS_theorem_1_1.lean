-- Prove2me | Theorems.Thm_LinearChoresCLS_theorem_1_1
-- name    : LinearChoresCLS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:48:02.303465+00:00
-- url     : https://prove2.me/theorems/e66a2536-a1d7-4dee-982d-27b8e520444e
-- title:
--   Theorem 1.1 — computing a competitive equilibrium of a linear Fisher market with chores is CLS-complete
-- statement:
--   It is CLS-complete to compute a competitive equilibrium of a Fisher market for chores with linear preferences.
--
--   Precisely, consider the search problem whose instances are linear Fisher markets with chores ($n\ge1$ agents, $m\ge1$ divisible chores, strictly positive rational disutilities, earning requirements and supplies) and whose answers are exact rational competitive equilibria $(p,z)$ in the sense of Definition 2.2. For some fixed exponent $k$, the version with answers of encoding length at most $(|x|+1)^k+k$ is in CLS, and every problem in CLS reduces to it by a polynomial-time search reduction:
--   $$
--   \exists k:\quad \textsf{ChoresCE}_{\le k}\in\mathrm{CLS}\quad\text{and}\quad \forall R\in\mathrm{CLS}:\ R\le_p\textsf{ChoresCE}_{\le k}.
--   $$
--
--   This is the first CLS-completeness result for a market equilibrium problem.
--
--   **Formalization Note** CLS, CLS-hardness and CLS-completeness are the public `InCLS`, `CLSHard`, `CLSComplete` (TFNP plus a polynomial-time Levin reduction to 3D-Continuous-Localopt, on Cook's machines).
--
--   Differences from the source:
--   - reading: "It is CLS-complete to compute a competitive equilibrium" → ∃ k, CLSComplete (bounded choresCESearch k); reason: CLS membership needs polynomially bounded answers; the exponent is fixed before all instances, as in the platform's other CLS-completeness goals
--   - encoding: a Fisher market for chores with linear preferences, as input → a binary encoding of a market with n ≥ 1 agents, m ≥ 1 chores and positive rational data; answers: encodings of exact rational equilibria (p, z); reason: the standard input model of the problem; the paper's instances (p.5, p.11)
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Theorem 1.1 (Main result)** (Liu–Ma–Tao–Yang–Zheng, *Competitive Equilibrium for Linear
Chores is CLS-complete*, arXiv:2611.06589, held version sha256 85d34a9e…, p.4): it is CLS-complete
to compute a competitive equilibrium of a Fisher market for chores with linear preferences.

For some fixed exponent `k`, the search problem "given a linear Fisher market with chores (`n ≥ 1`
agents, `m ≥ 1` divisible chores, strictly positive rational disutilities, earning requirements and
supplies), output an exact rational competitive equilibrium `(p, z)` (Definition 2.2)", with answers
of length at most `(|x| + 1)^k + k`, is in CLS, and every CLS problem reduces to it.

**Formalization Note.** CLS, CLS-hardness and CLS-completeness are the public
`NetworkEquilibriumCLS.LinearNash.InCLS`/`CLSHard`/`CLSComplete` (TFNP plus a polynomial-time Levin
reduction to 3D-Continuous-Localopt). The exponent `k` is chosen once, before all instances. -/
theorem theorem_1_1 : ∃ k : ℕ, CLSComplete (bounded choresCESearch k) := by sorry

end LinearChoresCLS
