-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_symExcess_strictConvexOn
-- name    : LightningNetwork.RateBounds.symExcess_strictConvexOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:53:21.118576+00:00
-- url     : https://prove2.me/theorems/d883cb4d-d34e-4381-be0c-0480d38789f0
-- title:
--   Proof of Theorem 2(ii): the excess cost $G(l_1,l_2)$ is strictly convex
-- statement:
--   Let $\alpha > 1$, $B > 0$ and $C \in \mathbb R$. The function
--
--   $$
--   G(l_1,l_2) = l_1 + l_2 + \frac{B(\alpha^{l_1}+\alpha^{l_2})}{(\alpha^{l_1}-1)(\alpha^{l_2}-1)} - \frac{2C\alpha}{(\alpha-1)^2}
--   $$
--
--   is strictly convex on the open quadrant $\{(l_1,l_2) : l_1 > 0,\ l_2 > 0\}$.
--
--   Strict convexity gives uniqueness of the minimizer, which by symmetry lies on the diagonal $l_1 = l_2$.
--
--   Differences from the source:
--   - encoding: α = α₊ at λ1 = λ2 = λ, with λ, r > 0 → α is a real parameter with α > 1; reason: α₊ + 1/α₊ = 2 + r/λ, so r/λ ↦ α₊ is a bijection of (0, ∞) onto (1, ∞); the instances are the same
--   - generalization: C > 0 (the cost of an on-chain transaction) → C any real number; reason: C enters G only as an additive constant, which does not affect convexity
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), unnumbered step, p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_symExcess

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(ii), unnumbered step: the excess cost is strictly convex.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), p. 11: "It is easy to check that this function is strictly
convex, as the trace and the determinant of its Hessian are both positive."

For `α > 1`, a reset cost `B > 0` and any `C`, the function
`(l1, l2) ↦ l1 + l2 + B(α^{l1} + α^{l2})/((α^{l1} − 1)(α^{l2} − 1)) − 2Cα/(α − 1)²`
is strictly convex on the open quadrant `l1 > 0, l2 > 0`.

**Formalization Note.** The domain is `(0, ∞) × (0, ∞)` (commitments are positive). -/
theorem symExcess_strictConvexOn (α B C : ℝ) (hα : 1 < α) (hB : 0 < B) :
    StrictConvexOn ℝ (Set.Ioi 0 ×ˢ Set.Ioi 0) (symExcess α B C) := by sorry

end LightningNetwork.RateBounds
