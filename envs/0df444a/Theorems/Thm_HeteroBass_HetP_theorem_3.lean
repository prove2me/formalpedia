-- Prove2me | Theorems.Thm_HeteroBass_HetP_theorem_3
-- name    : HeteroBass.HetP.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:04.450978+00:00
-- url     : https://prove2.me/theorems/8683f4ad-fe93-497a-b988-4dee1f89f442
-- title:
--   Theorem 3 — heterogeneous external rates strictly slow adoption
-- statement:
--   Consider a complete graph of $M$ consumers with nonnegative external adoption rates $p_i$ that are not all equal. Every consumer has the same positive total incoming influence $q$, divided equally among the other $M-1$ consumers. Set $\bar p=M^{-1}\sum_i p_i$. For every $t>0$,
--
--   $$f^{\mathrm{het}}(t;\{p_i\},q)<f^{\mathrm{hom}}(t;\bar p,q,M).$$
--
--   Thus replacing unequal external rates by their mean strictly increases the expected adopted fraction at each positive time.
--
--   **Formalization Note** Heterogeneity means that some $p_i$ differ; this also forces $M\ge2$. Nonnegative $p_i$ make the adoption rates valid. The comparison uses the generator-defined expected fraction, starting with no adopters.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Theorem 3, p. 11

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

namespace HeteroBass.HetP

/-- Theorem 3: heterogeneous external influence slows expected adoption at every positive time. -/
theorem theorem_3 (M : ℕ) (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hhetero : ∃ i j, p i ≠ p j)
    (q : ℝ) (hq : 0 < q) (t : ℝ) (ht : 0 < t) :
    expectedFraction p (completeQ (fun _ : Fin M => q)) t <
      expectedFraction (fun _ : Fin M => mean p)
        (completeQ (fun _ : Fin M => q)) t := by sorry

end HeteroBass.HetP
