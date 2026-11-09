-- Prove2me | Theorems.Thm_MatchingGFT_TightE_proposition_4_3
-- name    : MatchingGFT.TightE.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:21.20069+00:00
-- url     : https://prove2.me/theorems/a6b79888-f8c0-42a4-9d7f-54c525e75726
-- title:
--   Proposition 4.3 — Asymptotic behavior
-- statement:
--   For fixed $L\ge2$, as $N\to\infty$ in the market $(L,N)$: $\mathrm{FB}_{L,N}/N\to g_L$, and $E[\mathrm{GFT}(\mathrm{GSOM}_{L,N})]/N$, $E[\mathrm{GFT}(\mathrm{GBOM}_{L,N})]/N$, $\Pi^S(\mathrm{GSOM}_{L,N})/N$, $\Pi^B(\mathrm{GBOM}_{L,N})/N\to d_L$.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
--   - encoding: a limit in N of the ratio by N → Tendsto along ℕ of a real division, whose value at N = 0 is irrelevant; reason: limits ignore N = 0
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Proposition 4.3, PDF p. 21

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Mechanism
import Definitions.Def_MatchingGFT_TightE_CappedExp

open Filter Topology

namespace MatchingGFT.TightE

/-- Proposition 4.3 (PDF p. 21): for fixed `L ≥ 2`, as `N → ∞`, in the market `(L, N)` and for any strict
tie-breaking orders, `FB/N → g_L` and `E[GFT(GSOM)]/N`, `E[GFT(GBOM)]/N`, `Π^S(GSOM)/N`, `Π^B(GBOM)/N → d_L`. -/
theorem proposition_4_3 (L : ℝ) (hL : 2 ≤ L)
    (rank : ∀ N : ℕ, Finset (Fin (N + 1) × Fin (N + 1)) → ℕ)
    (hrank : ∀ N, IsTieOrder (cappedMarket L N) (rank N)) :
    Tendsto (fun N : ℕ => firstBestValue (cappedMarket L N) (rank N) / N) atTop (𝓝 (cappedG L)) ∧
    Tendsto (fun N : ℕ => expectedGFT (cappedMarket L N) (gsom (cappedMarket L N) (rank N)) / N)
      atTop (𝓝 (cappedD L)) ∧
    Tendsto (fun N : ℕ => expectedGFT (cappedMarket L N) (gbom (cappedMarket L N) (rank N)) / N)
      atTop (𝓝 (cappedD L)) ∧
    Tendsto (fun N : ℕ => profitS (cappedMarket L N) (gsom (cappedMarket L N) (rank N)) / N)
      atTop (𝓝 (cappedD L)) ∧
    Tendsto (fun N : ℕ => profitB (cappedMarket L N) (gbom (cappedMarket L N) (rank N)) / N)
      atTop (𝓝 (cappedD L)) := by sorry

end MatchingGFT.TightE
