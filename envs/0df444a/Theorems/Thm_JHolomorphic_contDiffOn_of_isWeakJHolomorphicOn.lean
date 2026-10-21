-- Prove2me | Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
-- name    : JHolomorphic.contDiffOn_of_isWeakJHolomorphicOn
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T20:31:31.397979+00:00
-- url     : https://prove2.me/theorems/1e13dbcb-7cdb-4cd7-b2cd-76f81e65e1b9
-- title:
--   Weak solutions of the nonlinear Cauchy–Riemann equation are smooth
-- statement:
--   Let $p>2$, let $E$ be a finite-dimensional real vector space and let $J$ be a smooth almost complex structure on an open set $O\subseteq E$. Let $U\subseteq\mathbb{C}$ be open and let $u:U\to O$ be continuous, with $u\in W^{1,p}_{\mathrm{loc}}(U)$ and
--   $$\partial_su+J(u)\,\partial_tu=0\quad\text{almost everywhere on }U$$
--   for its weak partial derivatives. Then $u$ is $C^\infty$ on $U$.
--
--   **Formalization Note** The hypothesis is `IsWeakJHolomorphicOn p J O U u`. Wendl states the result on the unit disc for $E=O=\mathbb{C}^n$ with the normalization $J(0)=i$, $u(0)=0$; here the domain is any open $U$, $J$ is only defined on $O$, and no normalization is imposed. Continuity of $u$ selects the continuous representative; the conclusion is `ContDiffOn ℝ ∞ u U`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Theorem 2.22 (1), p. 35 (case k = 1)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Theorem 2.22 (1) (p. 35), case `k = 1`: let `p > 2` and let `J` be a smooth almost
complex structure on an open set `O ⊆ E`. A map `u ∈ W^{1,p}_loc(U)` on an open set `U ⊆ ℂ`,
continuous with values in `O`, that satisfies `∂ₛu + J(u) ∂ₜu = 0` almost everywhere, is `C^∞` on
`U`. (Wendl works on the disc with `E = ℂⁿ`, `O = ℂⁿ`, `J(0) = i` and `u(0) = 0`.) -/
theorem contDiffOn_of_isWeakJHolomorphicOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    ContDiffOn ℝ ∞ u U := by
  sorry

end JHolomorphic
