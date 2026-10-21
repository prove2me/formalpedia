-- Prove2me | Theorems.Thm_Multihoming_Thresholds_proposition2_thresholds
-- name    : Multihoming.Thresholds.proposition2_thresholds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:50.576436+00:00
-- url     : https://prove2.me/theorems/1bbdab22-4a59-4c7f-83bd-345acc246cdf
-- title:
--   Proposition 2, PDF p. 20 (printed p. 14) — under partial multihoming, network effects raise the price iff e < e_p and the profit iff e < e_π, with e_π > e_p
-- statement:
--   Consider the symmetric Hotelling model with endogenous multihoming: mismatch cost $t>0$, network-effect strength $\mu$ with $0<\mu<t$, and exclusive features $e$ for both goods. Let $p^M(\mu)$ and $\pi^M(\mu)$ be the symmetric partial-multihoming price (26) and profit (price times the multihoming demand (14)), with $p^M(0)=e/2$ and $\pi^M(0)=e^2/(4t)$ the case without network effects. Assume partial multihoming, $e\in[\underline e,\overline e]$, with $\underline e=(t-\mu)(2t+\mu)/(2t)$ and $\overline e=(2t^2-\mu^2)/t$. Let
--   $$e_p=2(t-\mu),\qquad e_\pi=\frac{4t^2(t-\mu)+2t(2t-\mu)\sqrt{t^2-\mu^2}}{4t^2-3t\mu+\mu^2}.$$
--   Then
--
--   1. prices are higher with network externalities if $e<e_p$ and lower if $e>e_p$: $e<e_p\Rightarrow p^M(0)<p^M(\mu)$ and $e>e_p\Rightarrow p^M(\mu)<p^M(0)$;
--   2. profits are larger with network externalities if $e<e_\pi$ and lower if $e>e_\pi$: $e<e_\pi\Rightarrow \pi^M(0)<\pi^M(\mu)$ and $e>e_\pi\Rightarrow \pi^M(\mu)<\pi^M(0)$;
--   3. $e_\pi>e_p$.
--
--   So network effects raise prices and profits unless the goods have many exclusive features, and for $e\in(e_p,e_\pi)$ they lower the price yet raise the profit, because larger sales overcompensate.
--
--   **Formalization Note** "Assume partial multihoming" is the parameter range $e\in[\underline e,\overline e]$ of (23)–(24), not the claim that the symmetric price is a Nash equilibrium of the full game (Proposition 4, not posed). "With network externalities" means $\mu>0$. Standing assumptions: $t>0$ and $\mu<t$ (Assumption 1 (i)). Both thresholds lie inside $[\underline e,\overline e]$, so every branch is attained.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 20 (printed p. 14), Proposition 2; proof Appendix A1, PDF pp. 27–28

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model

namespace Multihoming.Thresholds

theorem proposition2_thresholds (t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t)
    (hlo : eLow t μ ≤ e) (hhi : e ≤ eBar t μ) :
    (e < eP t μ → pM t 0 e < pM t μ e) ∧ (eP t μ < e → pM t μ e < pM t 0 e) ∧
    (e < ePi t μ → piM t 0 e < piM t μ e) ∧ (ePi t μ < e → piM t μ e < piM t 0 e) ∧
    eP t μ < ePi t μ := by sorry

end Multihoming.Thresholds
