-- Prove2me | Theorems.Thm_LinearChoresCLS_lemma_7_5
-- name    : LinearChoresCLS.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:56:04.175059+00:00
-- url     : https://prove2.me/theorems/f6c7ce80-3b36-4cca-97ce-d055106f356a
-- title:
--   Lemma 7.5 — right derivatives of the normalized price family
-- statement:
--   Let $I=(A,c,\varepsilon)$ with $n\ge1$, $\varepsilon>0$. For every $x\in[0,1]^n$ and every feasible coordinate direction $\tilde v$ at $x$, the curve $h\mapsto\tilde p(x+h\tilde v)$ of normalized prices of the completed market has a finite right derivative at $h=0$:
--   $$
--   \lim_{h\downarrow0}\frac{\tilde p(x+h\tilde v)-\tilde p(x)}{h}\ \text{exists in }\mathbb R^M .
--   $$
--
--   This is property (a)(ii) of Proposition 4.1; the max–min rule is not differentiable at ties, but right derivatives exist everywhere.
--
--   **Formalization Note** The limit in $\mathbb R^M$ is taken coordinatewise (product topology).
--
--   Differences from the source: none.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Lemma 7.5, p.38

import Mathlib
import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Lemma 7.5 (Right derivatives of the price family)** (arXiv:2611.06589, held version sha256
85d34a9e…, p.38). For the completed market `f(I)` (`n ≥ 1`, `ε > 0`, parameters (7.1)), every
`x ∈ [0,1]ⁿ` and every feasible coordinate direction `ṽ` at `x`, the curve `h ↦ p̃(x + hṽ)` has a
finite right derivative at `h = 0`: `lim_{h↓0} (p̃(x + hṽ) − p̃(x))/h` exists in `ℝ^M`.

**Formalization Note.** The limit is taken in `Chore n L → ℝ` with the product topology, i.e.
coordinatewise; ties of the max–min rule are not excluded. -/
theorem lemma_7_5 {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) :
    ∀ x : Fin n → ℝ, InCube x → ∀ (i : Fin n) (s : Bool), FeasibleCoordDir x i s →
      ∃ D : Chore n (chainLength P ε) → ℝ,
        HasRightDerivAt0 (fun h => completedNormPrice P ε (x + h • coordDir i s)) D := by sorry

end LinearChoresCLS
