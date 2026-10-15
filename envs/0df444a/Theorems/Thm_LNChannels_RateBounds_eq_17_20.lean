-- Prove2me | Theorems.Thm_LNChannels_RateBounds_eq_17_20
-- name    : LNChannels.RateBounds.eq_17_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:23.781881+00:00
-- url     : https://prove2.me/theorems/ba94cdef-f7be-49c8-a3a0-a0ed1c56f527
-- title:
--   Eqs. (17)–(20), p. 11 — if $\kappa\ge(e^C-1)/B$ then $F(m)>0$ for every $m>0$
-- statement:
--   Let $B>0$, $\kappa>0$, $C\in\mathbb R$ and
--   $$F(m)=\frac{C}{1-e^{\kappa}}+\frac{B}{e^{\kappa m}-1}+m .$$
--   If
--   $$\kappa\ \ge\ \frac{e^{C}-1}{B},$$
--   then $F(m)>0$ for every real $m>0$.
--
--   With $\kappa=\log(1+r/\lambda)$, $F(m)$ is the cost of a unidirectional channel of size $m$ minus the on-chain cost $\lambda C/r$, so under this condition on-chain settlement is strictly cheaper than a unidirectional channel of any size. This is the sufficient condition (17)–(20) from which Theorem 2(i) follows.
--
--   **Formalization Note** The paper concludes "$F(\hat m)\ge0$ by (17)", but (17) is strict and the strict conclusion is what Theorem 2(i)'s strict inequality needs; the strict form is stated, for all $m>0$ rather than only at the minimizer $\hat m$. The paper's argument chooses $\alpha\le C/(C+1)$, which needs $C>0$; no sign is imposed on $C$ here, since for $C\le0$ every term of $F$ is nonnegative and $m>0$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 11 (PDF p. 12), proof of Theorem 2(i), eqs. (17)–(20)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- (17)–(20), p. 11: if `κ ≥ (e^C − 1)/B` then `F(m) = C/(1 − e^κ) + B/(e^{κm} − 1) + m` is
strictly positive for every `m > 0` (on-chain settlement is strictly cheaper than a unidirectional
channel of any size). -/
theorem eq_17_20 (B κ C : ℝ) (hB : 0 < B) (hκ : 0 < κ) (hκC : (Real.exp C - 1) / B ≤ κ) :
    ∀ m : ℝ, 0 < m → 0 < C / (1 - Real.exp κ) + B / (Real.exp (κ * m) - 1) + m := by sorry

end LNChannels.RateBounds
