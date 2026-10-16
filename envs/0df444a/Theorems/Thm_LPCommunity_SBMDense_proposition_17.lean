-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_proposition_17
-- name    : LPCommunity.SBMDense.proposition_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:39.401356+00:00
-- url     : https://prove2.me/theorems/93cae482-64b6-4d11-a17c-55a00598cac4
-- title:
--   Proposition 17, p. 29 — dense SBM with $1/(1-\omega)\notin\mathbb N$: $\rho_{\mathrm{avg}}$ and $\rho_{\max}$ are $\lceil 1/(1-\omega)\rceil$ w.h.p.
-- statement:
--   Let $p=\alpha n^{-\omega}$ and $q=\beta n^{-\omega}$ with $\alpha,\beta>0$ and $\omega\in(0,1)$ such that $\frac1{1-\omega}\notin\mathbb N$, and let $G\sim\mathcal G_{n,p,q}$. Then for every $\epsilon>0$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\Big[(1-\epsilon)\Big\lceil\frac1{1-\omega}\Big\rceil\le\rho_{\mathrm{avg}}(G)\le\rho_{\max}(G)=\Big\lceil\frac1{1-\omega}\Big\rceil\Big]=1.
--   $$
--
--   This is the distance input of Condition 2 of Theorem 7.
--
--   **Formalization Note** As printed, the proposition assumes only $\alpha,\beta>0$, not $\alpha>\beta$, and none is added. $n=2m$ runs over the even numbers; $\rho_{\max}$ is in `ℕ∞`, $\rho_{\mathrm{avg}}$ in $[0,\infty]$; the ceiling is `Nat.ceil`.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 29, Proposition 17

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs

open scoped ENNReal

namespace LPCommunity.SBMDense

theorem proposition_17 (α β ω : ℝ) (hα : 0 < α) (hβ : 0 < β) (hω0 : 0 < ω) (hω1 : ω < 1)
    (hk : ¬ ∃ k : ℕ, 1 / (1 - ω) = k) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (denseRegime α ω (2 * m)) (denseRegime β ω (2 * m))
        (fun _ G => ENNReal.ofReal ((1 - ε) * (⌈1 / (1 - ω)⌉₊ : ℝ)) ≤ LPCommunity.LPFail.rhoAvg G ∧
          LPCommunity.LPFail.rhoAvg G ≤ ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ℝ≥0∞) ∧ LPCommunity.LPFail.rhoMax G = (⌈1 / (1 - ω)⌉₊ : ℕ∞)))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMDense
