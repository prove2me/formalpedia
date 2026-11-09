-- Prove2me | Theorems.Thm_LinearChoresCLS_lemma_7_6
-- name    : LinearChoresCLS.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:55:46.896303+00:00
-- url     : https://prove2.me/theorems/fa61d939-8a2f-4d48-8060-1b4d821d3701
-- title:
--   Lemma 7.6 — total error bound $\beta=20t^3\le\alpha\varepsilon$
-- statement:
--   Let $I=(A,c,\varepsilon)$ with $n\ge1$, $\varepsilon>0$, let $\Phi(x)=\Psi(\tilde p(x))$ for the completed market $f(I)$, with $\alpha=\lambda t^2$ from (5.5) and $t$ from (7.1), and let $Q(x)=\frac12x^\top Ax+c^\top x$. There exist a constant $C\in\mathbb R$ and a function $R:[0,1]^n\to\mathbb R$ with
--   $$
--   \Phi(x)=C+\alpha Q(x)+R(x)\qquad (x\in[0,1]^n).
--   $$
--   Moreover $\beta:=20t^3$ satisfies $0\le\beta\le\alpha\varepsilon$, and $|R(x+he_i)-R(x)|\le\beta|h|$ for every $i\in[n]$ and every coordinate segment from $x$ to $x+he_i$ in $[0,1]^n$.
--
--   This is property (b) of Proposition 4.1 for the completed market.
--
--   Differences from the source:
--   - encoding: R : [0,1]ⁿ → ℝ → R : (Fin n → ℝ) → ℝ, with the identity (7.8) required only for x ∈ [0,1]ⁿ; reason: values off the box are never used; every function on the box extends
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Lemma 7.6, Eq. (7.8), p.39 (proof p.40)

import Mathlib
import Definitions.Def_LinearChoresCLS_PriceFamily

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Lemma 7.6 (Total error bound)** (arXiv:2611.06589, held version sha256 85d34a9e…, p.39). Let
`Φ(x) := Ψ(p̃(x))` for the completed market `f(I)` (`n ≥ 1`, `ε > 0`), with `α > 0` given by (5.5)
and `t` chosen as in (7.1). There exist a constant `C ∈ ℝ` and a function `R : [0,1]ⁿ → ℝ` such that
`Φ(x) = C + αQ(x) + R(x)` for every `x ∈ [0,1]ⁿ` (7.8). Moreover `β := 20t³` satisfies
`0 ≤ β ≤ αε`, and `|R(x + heᵢ) − R(x)| ≤ β|h|` for every `i ∈ [n]` and every coordinate segment from
`x` to `x + heᵢ` in `[0,1]ⁿ`.

**Formalization Note.** `Ψ` is the generic logarithmic objective of `completedMarket P ε`, `p̃` is
(7.2), and `Q(x) = ½xᵀAx + cᵀx` is the public `quadraticValue`. -/
theorem lemma_7_6 {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) :
    ∃ (C : ℝ) (R : (Fin n → ℝ) → ℝ),
      (∀ x, InCube x → (completedMarket P ε).Psi (completedNormPrice P ε x) =
        C + alpha P (tParam P ε) * quadraticValue P x + R x) ∧
      0 ≤ 20 * tParam P ε ^ 3 ∧ 20 * tParam P ε ^ 3 ≤ alpha P (tParam P ε) * ε ∧
      ∀ (x : Fin n → ℝ) (i : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single i (1 : ℝ)) →
        |R (x + h • Pi.single i (1 : ℝ)) - R x| ≤ 20 * tParam P ε ^ 3 * |h| := by sorry

end LinearChoresCLS
