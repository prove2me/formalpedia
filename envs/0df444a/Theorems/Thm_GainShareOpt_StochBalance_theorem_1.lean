-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_theorem_1
-- name    : GainShareOpt.StochBalance.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:27.529951+00:00
-- url     : https://prove2.me/theorems/8dab20b7-ca2e-4c57-8ead-fb4af318761a
-- title:
--   Theorem 1 — canonical representation for Stochastic Balance
-- statement:
--   Consider ST-BA$(f)$ for vertex-weighted OM-SR with unit offline capacities, adversarial arrivals and uniform vanishing success probabilities. For every $f\in F_0$, the certificate functional (44) satisfies
--   $$L[f]=\inf_{\ell\ge0,\ 0<\psi\le1,\ 0\le\tilde\psi\le\psi}\frac{\int_0^\ell e^{-z}f(z)\,dz+\int_\ell^{\ell+\tilde\psi}e^{-z}\,dz+(\psi-\tilde\psi)\bigl(1-f(\ell+\tilde\psi)\bigr)}{\psi}. \tag{6}$$
--   Here $\ell$ is an initial load on a target agent, $\psi$ the total load of the selected arrivals and $\tilde\psi$ the part that loads the target before the rest is diverted.
--
--   This reduces the implicit worst case over instances and dual constraints to three scalar parameters; every later result works with the right-hand side.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: finite bipartite instance G = (U, V, E) with weights w_u > 0, unit capacities, an adversarial arrival order fixed independently of the outcomes, at least one edge → Instance: offline agents Fin m, online agents Fin n listed in arrival order, neighbourhoods nbr v ⊆ Fin m, weights w > 0, a field asserting some edge; reason: an arbitrary arrival order is a relabelling of V, and the infimum ranges over all instances
--   - encoding: each assignment succeeds independently with probability p; expectation over the assignment outcomes → one independent Bernoulli(p) coin ω_v per arrival, used only if v is assigned; E_I is the finite sum Σ_ω Π_v p^{ω_v}(1−p)^{1−ω_v} · X(ω); reason: each arrival is assigned at most once, so this is the same distribution of outcomes
--   - reading: ties resolved by a fixed deterministic rule → ties go to the least index of Fin m; reason: the source does not specify the rule; since instances range over all labellings of U, this covers every fixed priority order on offline agents
--   - encoding: load ℓ_u = cumulative assignment probability on u → ℓ_u = p · (number of earlier arrivals assigned to u), the count kept in RunState.cnt; reason: every assignment increases the load by p (p. 21)
--   - encoding: inf over instances I of min over u ∈ U, S ⊆ N_u with p_u(S) > 0 → one sInf over all triples (I, u, S) with S ⊆ N_u and 0 < p_u(S); reason: inf of a min equals the inf over the union; the set is nonempty (one-edge instances) and bounded below by 0 for f ∈ F0
--   - encoding: liminf_{p↓0} → Filter.liminf along nhdsWithin 0 (Set.Ioi 0) of the real-valued worst ratio; reason: for p ∈ (0, 1) the worst ratio lies in [0, 1], so the real liminf is the source's
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 5, Theorem 1 (proof App. B, pp. 21–29)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical

namespace GainShareOpt.StochBalance

/-- Theorem 1 (canonical representation): for every `f ∈ F0`, the certificate functional (44)
equals the three-parameter infimum (6). -/
theorem theorem_1 (f : ℝ → ℝ) (hf : f ∈ F0) : certL f = canonicalL f := by sorry

end GainShareOpt.StochBalance
