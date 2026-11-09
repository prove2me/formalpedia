-- Prove2me | Theorems.Thm_LinearChoresCLS_lemma_7_4
-- name    : LinearChoresCLS.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:52:09.434205+00:00
-- url     : https://prove2.me/theorems/d096e151-0048-47ce-b8c1-fbd7ccacf5e2
-- title:
--   Lemma 7.4 — excluding undesignated choices
-- statement:
--   Let $I=(A,c,\varepsilon)$ with $n\ge1$, $\varepsilon>0$, and let $(p,z)$ be a competitive equilibrium of the completed market $f(I)$. Then
--   $$
--   p_{\max}\le(1+t)q_0p_0\qquad\text{and}\qquad p_{\min}\ge\frac{p_0}{q_0},
--   $$
--   with $q_0=1+t/4$. Consequently, no agent uses an undesignated choice: $z_{a\ell}>0$ only when $\ell$ is a designated choice of $a$.
--
--   With this lemma every gadget of the completed market satisfies the first hypothesis of Lemma 6.3.
--
--   Differences from the source:
--   - encoding: "agent a uses chore ℓ" → 0 < z a ℓ; reason: the paper's definition (p.32)
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Lemma 7.4, Eq. (7.6), p.35

import Mathlib
import Definitions.Def_LinearChoresCLS_CompletedMarket

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Lemma 7.4 (Excluding undesignated choices)** (arXiv:2611.06589, held version sha256
85d34a9e…, p.35). Let `(p, z)` be an equilibrium of the completed market `f(I)` (`n ≥ 1`, `ε > 0`,
parameters (7.1)). Then `p_max ≤ (1 + t) q₀ p₀` and `p_min ≥ p₀/q₀` (7.6). Consequently, no agent
uses an undesignated choice.

**Formalization Note.** `q₀ = 1 + t/4` (6.9); "agent `a` uses chore `ℓ`" is `z_{aℓ} > 0` (p.32);
the designated choices are those of Definition 6.1 and Section 5 (`Designated`). -/
theorem lemma_7_4 {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε)
    (p : Chore n (chainLength P ε) → ℝ) (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
    (hCE : (completedMarket P ε).IsCE p z) :
    pmax p ≤ (1 + tParam P ε) * qPar (tParam P ε) 0 * p (Sum.inl 0) ∧
      p (Sum.inl 0) / qPar (tParam P ε) 0 ≤ pmin p ∧
      ∀ a ℓ, 0 < z a ℓ → Designated a ℓ := by sorry

end LinearChoresCLS
