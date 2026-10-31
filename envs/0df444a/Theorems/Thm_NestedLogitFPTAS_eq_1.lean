-- Prove2me | Theorems.Thm_NestedLogitFPTAS_eq_1
-- name    : NestedLogitFPTAS.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:42.027006+00:00
-- url     : https://prove2.me/theorems/d5341046-315d-4de0-95e4-ca80fc83520b
-- title:
--   Eq. (1), p.7 — $\mathcal R(S)=\rho_{[1,M]}(S)/(w_0+\omega_{[1,M]}(S))$
-- statement:
--   For every assortment $S=(S_1,\dots,S_M)$,
--   $$
--   \mathcal R(S)=\frac{\rho_{[1,M]}(S)}{w_0+\omega_{[1,M]}(S)} .
--   $$
--   This representation of the revenue reduces the problem to tracking the two sums $\omega_{[1,M]}$ and $\rho_{[1,M]}$, which is what every later step does.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - generalization: S a C-feasible assortment → every assortment S; at w₀ = 0, S = ∅ both sides are 0; reason: the identity uses no feasibility, and it specializes to C-feasible S
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), §2.1, eq. (1), p.7

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), eq. (1), p.7: the revenue representation
`R(S) = ρ[1,M](S) / (w₀ + ω[1,M](S))`.

**Formalization Note.** Stated for every assortment; the paper's "C-feasible" plays no role. -/
theorem eq_1 {n M : ℕ} (I : Instance n M) (_hI : I.Standing) (S : Finset (Fin n)) :
    I.R S = I.rhoRange 1 M S / (I.w0 + I.omegaRange 1 M S) := by sorry

end NestedLogitFPTAS
