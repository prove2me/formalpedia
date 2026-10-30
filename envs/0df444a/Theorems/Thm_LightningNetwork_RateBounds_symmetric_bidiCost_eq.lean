-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_symmetric_bidiCost_eq
-- name    : LightningNetwork.RateBounds.symmetric_bidiCost_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:52:15.195878+00:00
-- url     : https://prove2.me/theorems/71bb6632-20ea-4f16-bb70-b83abd8733aa
-- title:
--   Proof of Theorem 2(ii): the cost of a symmetric bidirectional channel is $l_1 + l_2 + B(\alpha^{l_1}+\alpha^{l_2})/((\alpha^{l_1}-1)(\alpha^{l_2}-1))$
-- statement:
--   Let $\lambda > 0$, $r > 0$, commitments $l_1, l_2 > 0$ and $B \in \mathbb R$, and let $\alpha = \alpha_+$ be the root (4) at $\lambda_1 = \lambda_2 = \lambda$. Then
--
--   1. $\alpha = \dfrac{r + 2\lambda + \sqrt{r(4\lambda + r)}}{2\lambda}$;
--   2. $\alpha > 1$;
--   3. the cost (3) of the bidirectional channel at $\lambda_1 = \lambda_2 = \lambda$ is
--   $$
--   c^{l_1,l_2}(\lambda,\lambda) \;=\; l_1 + l_2 + \frac{B\,(\alpha^{l_1} + \alpha^{l_2})}{(\alpha^{l_1}-1)(\alpha^{l_2}-1)} .
--   $$
--
--   This is the specialization of Theorem 1(ii) to a symmetric channel used in the proof of Theorem 2(ii).
--
--   Differences from the source:
--   - encoding: the cost of a channel (Theorem 1) and of on-chain settlement (Lemma 1) → the closed forms (1), (3)–(4) and Cλ/r, as the definitions uniCost, bidiCost, onChainCost; reason: the proof uses Theorem 1 and Lemma 1 only through these formulas; their stochastic content is not formalized
--   - generalization: B > 0 (the cost of resetting a channel) → B any real number; reason: the identity is linear in B
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), unnumbered step, p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_alphaPlus
import Definitions.Def_LightningNetwork_RateBounds_bidiCost

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(ii), unnumbered step: the cost of a symmetric bidirectional channel.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), p. 11: "Setting λ2 = λ1 = λ in Theorem 1 (ii), it follows
that the cost of a symmetric bidirectional channel is
l1 + l2 + B(α^{l1} + α^{l2})/((α^{l1} − 1)(α^{l2} − 1)) where α := α+ = (r + 2λ + √(r(4λ + r)))/(2λ) > 1."

For `0 < lam`, `0 < r`, commitments `l1, l2 > 0` and any `B`, with `α = α₊(lam, lam, r)`:
1. `α = (r + 2 lam + √(r(4 lam + r)))/(2 lam)`;
2. `α > 1`;
3. the cost (3) at `λ1 = λ2 = lam` equals `l1 + l2 + B(α^{l1} + α^{l2})/((α^{l1} − 1)(α^{l2} − 1))`. -/
theorem symmetric_bidiCost_eq (lam r B l1 l2 : ℝ) (hlam : 0 < lam) (hr : 0 < r)
    (hl1 : 0 < l1) (hl2 : 0 < l2) :
    alphaPlus lam lam r = (r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam) ∧
      1 < alphaPlus lam lam r ∧
      bidiCost B r lam lam l1 l2 = l1 + l2
        + B * (alphaPlus lam lam r ^ l1 + alphaPlus lam lam r ^ l2)
          / ((alphaPlus lam lam r ^ l1 - 1) * (alphaPlus lam lam r ^ l2 - 1)) := by sorry

end LightningNetwork.RateBounds
