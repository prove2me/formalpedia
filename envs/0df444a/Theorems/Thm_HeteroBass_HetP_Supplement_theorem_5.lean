-- Prove2me | Theorems.Thm_HeteroBass_HetP_Supplement_theorem_5
-- name    : HeteroBass.HetP.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:29:07.604837+00:00
-- url     : https://prove2.me/theorems/1a5fe525-cba5-4e84-aa30-5a62e7e12deb
-- title:
--   Theorem 5 — commonly ordered external and incoming rates strictly slow adoption
-- statement:
--   Consider a complete network of $M\ge2$ consumers, initially with no adopters. External adoption rates satisfy $p_i\ge0$, incoming totals satisfy $q_i>0$, and every peer of node $j$ contributes $q_j/(M-1)$. Both arrays are genuinely heterogeneous: each has two unequal entries. Assume the common ordering stated in the source,
--
--   $$p_1\le\cdots\le p_M,\qquad q_1\le\cdots\le q_M.$$
--
--   Set $\bar p=M^{-1}\sum_i p_i$ and $\bar q=M^{-1}\sum_i q_i$. For the generator-defined expected adopter fractions and every finite $t>0$,
--
--   $$f^{\mathrm{het}}(t;\{p_i\},\{q_i\})<f^{\mathrm{hom}}(t;\bar p,\bar q,M).$$
--
--   This companion theorem treats joint heterogeneity with the source's common node ordering. Nonnegative covariance alone is not the stated hypothesis. Individual external rates may vanish; heterogeneity and nonnegativity imply positive total seeding. No assertion of independent inter-adoption times is assumed.
--
--   Differences from the source:
--   - encoding: nonnegative external rates, (7), genuine heterogeneity of both arrays and their common order on nodes 1 through M → nonnegative p, positive q, two explicit unequal pairs and Monotone p and Monotone q on Fin M with M≥2; reason: these bind the standing rate assumptions and exactly the displayed common order, allowing ties and zero external rates
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Theorem 5, p. 13; (9), p. 5; (34), p. 11

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

namespace HeteroBass.HetP.Supplement

theorem theorem_5 {M : ℕ} (hM : 2 ≤ M) (p q : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hphet : ∃ i j, p i ≠ p j) (hqhet : ∃ i j, q i ≠ q j)
    (hpord : Monotone p) (hqord : Monotone q) (t : ℝ) (ht : 0 < t) :
    expectedFraction p (completeQ q) t <
      expectedFraction (fun _ : Fin M => mean p)
        (completeQ (fun _ : Fin M => mean q)) t := by sorry

end HeteroBass.HetP.Supplement
