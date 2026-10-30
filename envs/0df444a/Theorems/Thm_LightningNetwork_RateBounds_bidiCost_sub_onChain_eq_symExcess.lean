-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_bidiCost_sub_onChain_eq_symExcess
-- name    : LightningNetwork.RateBounds.bidiCost_sub_onChain_eq_symExcess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:52:58.336258+00:00
-- url     : https://prove2.me/theorems/86f66e57-3260-4db9-8ab0-6dab40e18e1c
-- title:
--   Proof of Theorem 2(ii): the excess over on-chain is $G(l_1,l_2)$, with $2C\lambda/r = 2C\alpha/(\alpha-1)^2$
-- statement:
--   Let $\lambda > 0$, $r > 0$, $B, C \in \mathbb R$ and $\alpha = \alpha_+$ at $\lambda_1 = \lambda_2 = \lambda$. Then
--
--   1. the on-chain cost of the two payment streams is $\dfrac{2C\lambda}{r} = \dfrac{2C\alpha}{(\alpha-1)^2}$;
--   2. for all commitments $l_1, l_2 > 0$, the cost (3) of the symmetric channel minus $2C\lambda/r$ equals
--   $$
--   G(l_1,l_2) = l_1 + l_2 + \frac{B(\alpha^{l_1}+\alpha^{l_2})}{(\alpha^{l_1}-1)(\alpha^{l_2}-1)} - \frac{2C\alpha}{(\alpha-1)^2}.
--   $$
--
--   A symmetric channel is cheaper than on-chain settlement for some commitments exactly when $G$ takes a negative value.
--
--   Differences from the source:
--   - encoding: the cost of a channel (Theorem 1) and of on-chain settlement (Lemma 1) → the closed forms (1), (3)–(4) and Cλ/r, as the definitions uniCost, bidiCost, onChainCost; reason: the proof uses Theorem 1 and Lemma 1 only through these formulas; their stochastic content is not formalized
--   - generalization: B > 0 (the cost of resetting a channel) → B any real number; reason: the identity is linear in B
--   - generalization: C > 0 (the cost of an on-chain transaction) → C any real number; reason: the identity is linear in C
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), unnumbered step, p. 11

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_alphaPlus
import Definitions.Def_LightningNetwork_RateBounds_bidiCost
import Definitions.Def_LightningNetwork_RateBounds_onChainCost
import Definitions.Def_LightningNetwork_RateBounds_symExcess

namespace LightningNetwork.RateBounds

/-- **Proof of Theorem 2(ii), unnumbered step: the excess over on-chain in terms of α.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), p. 11: "Subtracting from such cost the cost of on-chain
transactions instead, which is 2Cλ/r, and rewriting λ/r in terms of α, the difference is
l1 + l2 + B(α^{l1} + α^{l2})/((α^{l1} − 1)(α^{l2} − 1)) − 2Cα/(α − 1)²."

For `0 < lam`, `0 < r`, any `B`, `C`, with `α = α₊(lam, lam, r)`:
1. the on-chain cost of the two streams is `2Cλ/r = 2Cα/(α − 1)²`;
2. for commitments `l1, l2 > 0`, the cost (3) at `λ1 = λ2 = lam` minus `2Cλ/r` is
   `symExcess α B C (l1, l2)`. -/
theorem bidiCost_sub_onChain_eq_symExcess (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    2 * onChainCost C r lam = 2 * C * alphaPlus lam lam r / (alphaPlus lam lam r - 1) ^ 2 ∧
      ∀ l1 l2 : ℝ, 0 < l1 → 0 < l2 →
        bidiCost B r lam lam l1 l2 - 2 * onChainCost C r lam
          = symExcess (alphaPlus lam lam r) B C (l1, l2) := by sorry

end LightningNetwork.RateBounds
