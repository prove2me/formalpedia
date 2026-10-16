-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_proposition_12
-- name    : LPCommunity.SBMDense.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:25.678831+00:00
-- url     : https://prove2.me/theorems/bcf98910-664f-46e1-8510-553b00ca2c33
-- title:
--   Proposition 12, p. 28 — the diameter of $\mathcal G_{n,\alpha n^{-\omega}}$ is $1+\lfloor 1/(1-\omega)\rfloor$ w.h.p.
-- statement:
--   Let $\omega\in[0,1)$ and $\alpha>0$, with $\alpha<1$ if $\omega=0$, and let $G\sim\mathcal G_{n,p}$ with $p=\alpha n^{-\omega}$. Writing $\lfloor x\rfloor$ for the greatest integer not exceeding $x$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\Big[\rho_{\max}(G)=1+\Big\lfloor\frac{1}{1-\omega}\Big\rfloor\Big]=1.
--   $$
--
--   For $\omega\in[0,\tfrac12)$ the diameter is $2$; it grows by one each time $\frac1{1-\omega}$ crosses an integer. Together with Proposition 11 this gives the diameter of the dense stochastic block model in Propositions 16–18.
--
--   **Formalization Note** The diameter takes values in `ℕ∞`, so the event excludes disconnected graphs (diameter $+\infty$). The floor is `Nat.floor`. The edge probability is clamped into $[0,1]$, which matters only for finitely many $n$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 28, Proposition 12

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs

namespace LPCommunity.SBMDense

theorem proposition_12 (α ω : ℝ) (hα : 0 < α) (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (hα1 : ω = 0 → α < 1) :
    Filter.Tendsto
      (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (denseRegime α ω n)
        (fun G => LPCommunity.LPFail.rhoMax G = ((1 + ⌊1 / (1 - ω)⌋₊ : ℕ) : ℕ∞)))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMDense
