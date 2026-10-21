-- Prove2me | Theorems.Thm_LNChannels_Walk_proposition_2_limits
-- name    : LNChannels.Walk.proposition_2_limits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:04.885869+00:00
-- url     : https://prove2.me/theorems/dbafd505-1025-4c8c-b63e-8093a58ec959
-- title:
--   Proposition 2 (i)–(ii), p. 9 — the ratio tends to l₁ as q ↓ 0 and to l₁l₂ as q → 1
-- statement:
--   Let $l_1,l_2\ge1$ be integers, and let
--   $$
--   R(q)=\frac{(q+1)\Bigl(\bigl(l_2(q^{l_1}-1)-l_1\bigr)q^{l_2}+l_1\Bigr)}{(q-1)(q^{l_1+l_2}-1)}
--   $$
--   be the long-run number of channel transactions per on-chain transaction of Proposition 2, as a function of $q=\lambda_2/\lambda_1$. Then:
--
--   1. (unidirectional channel) $R(q)\to l_1$ as $q\downarrow0$;
--   2. (symmetric bidirectional channel) $R(q)\to l_1l_2$ as $q\to1$, $q\neq1$.
--
--   A unidirectional channel thus reduces on-chain traffic in proportion to its size, and a symmetric bidirectional channel in proportion to the product of the two sizes.
--
--   **Formalization Note** The paper writes "(q ↓ 0)" and "(q → 1)", and both statements are limits of the closed form. The limit at $q\to1$ is taken along $q\neq1$, where the formula is defined. The walks at $q=0$ or $q=1$ are not involved.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 9 (PDF 10), Proposition 2 (i)–(ii)

import Mathlib

namespace LNChannels.Walk

open Filter Topology

/-- Proposition 2 (i)–(ii), p. 9: the closed form
`R(q) = (q + 1)((l₂(q^{l₁} − 1) − l₁) q^{l₂} + l₁)/((q − 1)(q^{l₁+l₂} − 1))` tends to `l₁` as
`q ↓ 0` (unidirectional channel) and to `l₁ l₂` as `q → 1` (symmetric channel). -/
theorem proposition_2_limits (l₁ l₂ : ℕ) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂) :
    Tendsto (fun q : ℝ => (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
        ((q - 1) * (q ^ (l₁ + l₂) - 1))) (𝓝[>] 0) (𝓝 (l₁ : ℝ)) ∧
    Tendsto (fun q : ℝ => (q + 1) * (((l₂ : ℝ) * (q ^ l₁ - 1) - l₁) * q ^ l₂ + l₁) /
        ((q - 1) * (q ^ (l₁ + l₂) - 1))) (𝓝[≠] 1) (𝓝 ((l₁ : ℝ) * l₂)) := by sorry

end LNChannels.Walk
