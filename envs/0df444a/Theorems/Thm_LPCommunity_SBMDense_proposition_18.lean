-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_proposition_18
-- name    : LPCommunity.SBMDense.proposition_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:19.704955+00:00
-- url     : https://prove2.me/theorems/42023b8a-45f8-40b2-b45f-8d367df74d89
-- title:
--   Proposition 18, p. 30 — dense SBM with $1/(1-\omega)\in\mathbb N$: $\rho_{\max}=1/(1-\omega)+1$ and $\rho_{\mathrm{avg}}\gtrsim 1/(1-\omega)+e^{-\alpha^{1/(1-\omega)}}$ w.h.p.
-- statement:
--   Let $p=\alpha n^{-\omega}$ and $q=\beta n^{-\omega}$ with $\alpha>\beta>0$ and $\omega\in(0,1)$ such that $\frac1{1-\omega}\in\mathbb N$, and let $G\sim\mathcal G_{n,p,q}$. Then for every $\epsilon>0$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\Big[(1-\epsilon)\Big(\frac1{1-\omega}+\exp\big(-\alpha^{\frac1{1-\omega}}\big)\Big)\le\rho_{\mathrm{avg}}(G)\le\rho_{\max}(G)=\frac1{1-\omega}+1\Big]=1.
--   $$
--
--   This is the distance input of Conditions 3 and 4 of Theorem 7.
--
--   **Formalization Note** $n=2m$ runs over the even numbers. $\rho_{\max}$ is in `ℕ∞` and is compared with the real number $\frac1{1-\omega}+1$ in $[0,\infty]$ via `ENNReal.ofReal`; $\rho_{\mathrm{avg}}$ is in $[0,\infty]$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 30, Proposition 18

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs

open scoped ENNReal

namespace LPCommunity.SBMDense

theorem proposition_18 (α β ω : ℝ) (hβ : 0 < β) (hαβ : β < α) (hω0 : 0 < ω) (hω1 : ω < 1)
    (hk : ∃ k : ℕ, 1 / (1 - ω) = k) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (denseRegime α ω (2 * m)) (denseRegime β ω (2 * m))
        (fun _ G => ENNReal.ofReal ((1 - ε) * (1 / (1 - ω) + Real.exp (-(α ^ (1 / (1 - ω)))))) ≤
            LPCommunity.LPFail.rhoAvg G ∧
          LPCommunity.LPFail.rhoAvg G ≤ ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ℝ≥0∞) ∧
          ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (1 / (1 - ω) + 1)))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMDense
