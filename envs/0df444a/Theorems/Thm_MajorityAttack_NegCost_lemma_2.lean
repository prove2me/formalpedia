-- Prove2me | Theorems.Thm_MajorityAttack_NegCost_lemma_2
-- name    : MajorityAttack.NegCost.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:29.436551+00:00
-- url     : https://prove2.me/theorems/74445f6a-ef47-4b22-823f-a769cfaf23a9
-- title:
--   Lemma 2 — congestion raises the attack-chain fee per block
-- statement:
--   Let $\mu$ be a nonnegative, non-degenerate probability distribution of transaction fees with a finite first moment. Each block holds $b\ge1$ transactions. Suppose $n>b$ transactions are available to an honest block, while $n'>n$ are available to a slower attack-chain block. Users keep the same fee distribution on both chains. Then
--
--   $$\Phi_b(n')>\Phi_b(n),$$
--
--   where $\Phi_b(k)$ is the expected sum of the $b$ highest fees among $k$ independent transactions. This is the strict fee comparison used in Proposition 1.
--
--   **Formalization Note** The paper writes congestion as $\tau\sigma>b$ and derives more arrivals on the attacking chain from $h_A<H$. Here the arrivals are natural counts $b<n<n'$. Non-degeneracy and integrability make explicit the qualifications in the proof on p. 13.
-- source:
--   Gans & Halaburda, “Zero Cost” Majority Attacks on Permissionless Blockchains, arXiv:2308.06568v1, pp. 12–13, Lemma 2

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Fees

namespace MajorityAttack.NegCost

/-- Lemma 2, pp. 12–13: congestion and slower attack blocks increase expected fees. -/
theorem lemma_2 (μ : MeasureTheory.Measure ℝ) (hμ : FeeLaw μ)
    (b n n' : ℕ) (hb : 0 < b) (hbn : b < n) (hnn' : n < n') :
    blockFees μ b n < blockFees μ b n' := by sorry

end MajorityAttack.NegCost
