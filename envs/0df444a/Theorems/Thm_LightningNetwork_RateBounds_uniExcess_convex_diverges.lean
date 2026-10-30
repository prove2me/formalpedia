-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_uniExcess_convex_diverges
-- name    : LightningNetwork.RateBounds.uniExcess_convex_diverges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:50.958921+00:00
-- url     : https://prove2.me/theorems/cfa797c3-6200-4343-a500-cf02b47f0f6f
-- title:
--   Proof of Theorem 2(i): $F$ is convex on $(0,\infty)$ and diverges as $m \to 0$ and $m \to \infty$
-- statement:
--   Let $B > 0$, $\kappa > 0$ and $C \in \mathbb R$, and let $F(m) = C/(1-e^\kappa) + B/(e^{\kappa m}-1) + m$. Then
--
--   1. $F$ is convex on $(0, \infty)$;
--   2. $F(m) \to +\infty$ as $m \to 0^+$;
--   3. $F(m) \to +\infty$ as $m \to \infty$.
--
--   Together these give the existence of a minimizer of $F$ on $(0,\infty)$.
--
--   Differences from the source:
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
--   - generalization: C > 0 (the cost of an on-chain transaction) → C any real number; reason: C enters F only as the additive constant C/(1 − e^κ), which affects neither convexity nor divergence
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), unnumbered step, p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniExcess

open Filter Topology

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(i), unnumbered step: F is convex and diverges at 0 and ∞.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), p. 11: "F(m) = C/(1 − e^κ) + B/(e^{κm} − 1) + m. It is immediate
to see that such a function (i) is convex, and (ii) diverges to +∞ as m approaches 0 or ∞."

For `0 < B` (a reset cost), `0 < κ` (the paper's `κ = log(1 + r/λ)`) and any `C`, the function
`F = uniExcess κ B C` is convex on `(0, ∞)`, tends to `+∞` as `m → 0⁺`, and tends to `+∞` as
`m → ∞`.

**Formalization Note.** "As m approaches 0" is the right limit `𝓝[>] 0` (the domain is
`m > 0`). -/
theorem uniExcess_convex_diverges (κ B C : ℝ) (hB : 0 < B) (hκ : 0 < κ) :
    ConvexOn ℝ (Set.Ioi 0) (uniExcess κ B C) ∧
      Tendsto (uniExcess κ B C) (𝓝[>] 0) atTop ∧
      Tendsto (uniExcess κ B C) atTop atTop := by sorry

end LightningNetwork.RateBounds
