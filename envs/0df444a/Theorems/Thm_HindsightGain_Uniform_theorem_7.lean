-- Prove2me | Theorems.Thm_HindsightGain_Uniform_theorem_7
-- name    : HindsightGain.Uniform.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:00.192199+00:00
-- url     : https://prove2.me/theorems/2cd206d1-47a9-4a85-8ab6-0c34958c39e4
-- title:
--   Theorem 7 — Maurer vector contraction
-- statement:
--   Let $n\ge1$, let $S$ be countable, and for $1\le i\le n$ let $\psi_i:S\to\mathbb R$ and $\phi_i:S\to\ell_2$ satisfy
--   $$\psi_i(s)-\psi_i(s')\le\|\phi_i(s)-\phi_i(s')\|_2\qquad(s,s'\in S).$$
--   For independent fair Rademacher signs, the full vector-contraction inequality is
--   $$\mathbb E\sup_{s\in S}\sum_i\epsilon_i\psi_i(s)\le\sqrt2\,\mathbb E\sup_{s\in S}\sum_{i,k}\epsilon_{ik}\phi_i(s)_k.$$
--   The coordinate series are ordered partial-sum limits, and expectations are signed extended expectations. Infinite positive expected suprema are allowed. For the empty class both expected suprema are $-\infty$. This is the source's infinite-dimensional contraction tool, with no uniform norm bound or integrability assumption on either supremum.
--
--   Differences from the source:
--   - encoding: independent Rademacher sequences → canonical product laws of fair Boolean signs, transformed to ±1; reason: the expected suprema depend only on the independent sign laws
--   - encoding: ℓ₂ outputs and their random-sign series → Mathlib lp of real sequences at exponent 2 and ordered partial-sum limits, set to 0 only on the null nonconvergence event; reason: square summability gives almost-sure convergence and countability gives one common full-measure event
--   - encoding: possibly infinite expected suprema, including an empty class → EReal suprema and positive-part integral minus negative-part integral, with empty supremum -∞; reason: a nonempty countable class has an integrable mean-zero lower bound, so no undefined infinity subtraction occurs
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 7 (Maurer [Mau16, Theorem 3, preprint]), p.16

import Mathlib
import Definitions.Def_HindsightGain_Uniform_rademacher

set_option autoImplicit false

namespace HindsightGain.Uniform

/-- Theorem 7, p.16: countable classes, full real l2, and extended expectations.
The empty class has both expected suprema -∞. No integrability or boundedness is assumed. -/
theorem theorem_7 {S : Type} [Countable S] (n : ℕ) (hn : 1 ≤ n)
    (ψ : Fin n → S → ℝ) (φ : Fin n → S → SequenceL2)
    (h : ∀ i s s', ψ i s - ψ i s' ≤ ‖φ i s - φ i s'‖) :
    scalarComplexity n ψ ≤ (Real.sqrt 2 : EReal) * vectorComplexity n φ := by sorry

end HindsightGain.Uniform
