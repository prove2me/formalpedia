-- Prove2me | Theorems.Thm_HeteroBass_HetP_Supplement_theorem_4
-- name    : HeteroBass.HetP.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:28:31.587205+00:00
-- url     : https://prove2.me/theorems/a30438b9-db3a-4efe-9bd2-a814e8777e99
-- title:
--   Theorem 4 (corrected: positive seeding) — mild incoming heterogeneity strictly slows adoption
-- statement:
--   Consider a complete network with $M\ge2$ consumers. Each consumer has the same positive external adoption rate $p>0$. Consumer $j$ has total incoming influence $q_j>0$, shared equally among its $M-1$ peers, so $Q_{k,j}=q_j/(M-1)$ for $k\ne j$. Suppose at least two values $q_j$ differ, and write $\bar q=M^{-1}\sum_j q_j$. Let $f$ be the expected adopter fraction of the initially empty Bass process. Then, for every finite $t>0$,
--
--   $$f^{\mathrm{het}}(t;p,\{q_j\})<f^{\mathrm{hom}}(t;p,\bar q,M).$$
--
--   This companion theorem compares mild heterogeneity in incoming influence with the homogeneous network of the same mean. It does not require an ordering of the incoming rates, nor does it cover arbitrary edge heterogeneity. The printed independence argument is not a hypothesis of this theorem.
--
--   Differences from the source:
--   - correction: Theorem 4 does not explicitly exclude p=0 → the common external rate satisfies p>0; reason: at p=0 both initially empty networks stay empty and strictness fails; Appendix G, p. 31 asserts p(2M−3)/(M−1)² Var(q)>0, identifying the intended positive-seeding domain
--   - encoding: a complete network with heterogeneous positive incoming rates, indexed 1 through M → Fin M with M≥2, all q_i>0 and an explicit pair with unequal q_i; reason: these encode (7), the ordinary meaning of heterogeneity and the nonzero M−1 denominator; the printed lower index i=i is read as i=1, as in the conclusion
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Theorem 4, p. 12; Appendix G, p. 31

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

namespace HeteroBass.HetP.Supplement

theorem theorem_4 {M : ℕ} (hM : 2 ≤ M) (p : ℝ) (q : Fin M → ℝ)
    (hp : 0 < p) (hq : ∀ i, 0 < q i) (hhet : ∃ i j, q i ≠ q j)
    (t : ℝ) (ht : 0 < t) :
    expectedFraction (fun _ : Fin M => p) (completeQ q) t <
      expectedFraction (fun _ : Fin M => p)
        (completeQ (fun _ : Fin M => mean q)) t := by sorry

end HeteroBass.HetP.Supplement
