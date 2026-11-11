-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_theorem_3
-- name    : GainShareOpt.StochBalance.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:42.434166+00:00
-- url     : https://prove2.me/theorems/f1c16d6a-e136-409f-9e2d-cf121dd2738f
-- title:
--   Theorem 3 — the optimal Stochastic Balance certificate is attained in $F_2$ and $\Gamma(F_0)=\Gamma(F_1)=\Gamma(F_2)\in[0.5802,0.5805]$
-- statement:
--   Let $L[f]$ be the certificate functional (44) of the vertex-weighted Stochastic Balance template (configuration-LP benchmark, dual updates (43), uniform vanishing success probabilities), and $\Gamma(F)=\sup_{f\in F}L[f]$. Then:
--   1. the supremum defining $\Gamma(F_0)$ is attained by a function in $F_2$;
--   2. the three classes have the same optimal value, with
--   $$\Gamma(F_0)=\Gamma(F_1)=\Gamma(F_2)\in[0.5802,\ 0.5805].$$
--
--   The upper endpoint bounds every certificate obtainable by optimizing $f$ within this template; the lower endpoint is a certified guarantee; the equalities show that the restrictions defining $F_1$ and $F_2$ are lossless.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: finite bipartite instance G = (U, V, E) with weights w_u > 0, unit capacities, an adversarial arrival order fixed independently of the outcomes, at least one edge → Instance: offline agents Fin m, online agents Fin n listed in arrival order, neighbourhoods nbr v ⊆ Fin m, weights w > 0, a field asserting some edge; reason: an arbitrary arrival order is a relabelling of V, and the infimum ranges over all instances
--   - encoding: each assignment succeeds independently with probability p; expectation over the assignment outcomes → one independent Bernoulli(p) coin ω_v per arrival, used only if v is assigned; E_I is the finite sum Σ_ω Π_v p^{ω_v}(1−p)^{1−ω_v} · X(ω); reason: each arrival is assigned at most once, so this is the same distribution of outcomes
--   - reading: ties resolved by a fixed deterministic rule → ties go to the least index of Fin m; reason: the source does not specify the rule; since instances range over all labellings of U, this covers every fixed priority order on offline agents
--   - encoding: load ℓ_u = cumulative assignment probability on u → ℓ_u = p · (number of earlier arrivals assigned to u), the count kept in RunState.cnt; reason: every assignment increases the load by p (p. 21)
--   - encoding: inf over instances I of min over u ∈ U, S ⊆ N_u with p_u(S) > 0 → one sInf over all triples (I, u, S) with S ⊆ N_u and 0 < p_u(S); reason: inf of a min equals the inf over the union; the set is nonempty (one-edge instances) and bounded below by 0 for f ∈ F0
--   - encoding: liminf_{p↓0} → Filter.liminf along nhdsWithin 0 (Set.Ioi 0) of the real-valued worst ratio; reason: for p ∈ (0, 1) the worst ratio lies in [0, 1], so the real liminf is the source's
--   - encoding: Γ(F) = sup_{f∈F} L[f] → sSup of the image of F under certL; reason: L takes values in [0, 1] on F0, and F0, F1, F2 are nonempty
--   - encoding: [0.5802, 0.5805] → 2901/5000 ≤ Γ(F0) ≤ 1161/2000; reason: the same closed interval with exact rational endpoints
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 6, Theorem 3 (proof §6.2, pp. 18–19)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional

namespace GainShareOpt.StochBalance

/-- Theorem 3 (full-class certification and lossless restrictions): the supremum defining `Γ(F0)`
is attained by a function in `F2`, and `Γ(F0) = Γ(F1) = Γ(F2) ∈ [0.5802, 0.5805]`. -/
theorem theorem_3 :
    (∃ f ∈ F2, certL f = certCapacity F0) ∧
    certCapacity F0 = certCapacity F1 ∧ certCapacity F1 = certCapacity F2 ∧
    (2901 / 5000 : ℝ) ≤ certCapacity F0 ∧ certCapacity F0 ≤ 1161 / 2000 := by sorry

end GainShareOpt.StochBalance
