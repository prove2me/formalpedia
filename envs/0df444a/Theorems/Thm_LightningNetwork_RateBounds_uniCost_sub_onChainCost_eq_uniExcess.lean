-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_uniCost_sub_onChainCost_eq_uniExcess
-- name    : LightningNetwork.RateBounds.uniCost_sub_onChainCost_eq_uniExcess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:25.999044+00:00
-- url     : https://prove2.me/theorems/e102bb7a-1f5b-40f4-b465-d003454cf3d3
-- title:
--   Proof of Theorem 2(i): the excess cost of a unidirectional channel is $F(m)$
-- statement:
--   Let $\lambda > 0$ be the payment rate, $r > 0$ the interest rate, $B$ the reset cost and $C$ the on-chain cost, and put $\kappa = \log(1 + r/\lambda)$, so that $\lambda/r = (e^\kappa - 1)^{-1}$. For every channel size $m > 0$,
--
--   $$
--   m + B\left(\left(1 + \frac r\lambda\right)^{m} - 1\right)^{-1} - \frac{C\lambda}{r} \;=\; F(m) \;=\; \frac{C}{1-e^\kappa} + \frac{B}{e^{\kappa m}-1} + m .
--   $$
--
--   The left side is the cost (1) of a unidirectional channel of size $m$ minus the on-chain cost of Lemma 1. The identity turns the comparison in Theorem 2(i) into the sign of $F$.
--
--   Differences from the source:
--   - encoding: the cost of a channel (Theorem 1) and of on-chain settlement (Lemma 1) → the closed forms (1), (3)–(4) and Cλ/r, as the definitions uniCost, bidiCost, onChainCost; reason: the proof uses Theorem 1 and Lemma 1 only through these formulas; their stochastic content is not formalized
--   - generalization: B > 0 and C > 0 (costs of reset and of an on-chain transaction) → B and C any real numbers; reason: the identity is linear in B and in C; the statement specializes to B, C > 0
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), unnumbered step, p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniCost
import Definitions.Def_LightningNetwork_RateBounds_onChainCost
import Definitions.Def_LightningNetwork_RateBounds_uniExcess

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(i), unnumbered step: the excess cost is F(m).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), p. 11: "By Theorem 1 (i), the cost of a unidirectional
channel of size m is m + B((1 + r/λ)^m − 1)^{−1}. … which is λC/r by Lemma 1. … To find such an
infimum, denote by λ/r = (e^κ − 1)^{−1}, which allows to rewrite the function to minimize as
F(m) = C/(1 − e^κ) + B/(e^{κm} − 1) + m."

For `0 < lam`, `0 < r` and a channel size `m > 0`, with `κ = log(1 + r/lam)`:
`uniCost B r lam m − onChainCost C r lam = F(m)`. -/
theorem uniCost_sub_onChainCost_eq_uniExcess (lam r B C m : ℝ) (hlam : 0 < lam) (hr : 0 < r)
    (hm : 0 < m) :
    uniCost B r lam m - onChainCost C r lam = uniExcess (Real.log (1 + r / lam)) B C m := by sorry

end LightningNetwork.RateBounds
