-- Prove2me | Theorems.Thm_OLPRegret_lemma_9
-- name    : OLPRegret.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:16.683562+00:00
-- url     : https://prove2.me/theorems/48273dbc-b143-4bfb-ba1e-f43b9abb64c7
-- title:
--   Lemma 9 — the subgradient inequality for empirical shadow prices
-- statement:
--   For all $t$, $b\in\mathbb R^m_+$, $y\in\mathbb R^m_+$ and every minimizer $y_t^b$ of $\Lambda_t^b$ over $\mathbb R^m_+$,
--   $$
--   (y_t^b-y)'\dot\Lambda_t^b(y)\le0.
--   $$
--
--   Differences from the source:
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - encoding: $t\in\mathbb N$, division by $t$ → at $t=0$ the empty average is $0$, so $\Lambda_0^b(y)=b'y$; reason: the inequality still holds there; no instance with $t\ge1$ changes
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 9, Online Appendix p.26 (PDF 62)

import Mathlib
import Definitions.Def_OLPRegret_dualMin

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 9, Online Appendix p.26: `(yₜᵇ − y)′Λ̇ₜᵇ(y) ≤ 0` for all `t ∈ ℕ`,
`b ∈ ℝᵐ₊` and `y ∈ ℝᵐ₊`, here for every minimizer `yₜᵇ` of `Λₜᵇ`. -/
theorem lemma_9 {m t : ℕ} (s : Sample m t) (b y y' : E m) (hb : VNonneg b) (hy : VNonneg y)
    (hy' : y' ∈ dualMin s b) :
    inner ℝ (y' - y) (LambdaDot s b y) ≤ 0 := by sorry

end OLPRegret
