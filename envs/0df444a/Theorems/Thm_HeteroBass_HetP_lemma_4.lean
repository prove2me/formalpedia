-- Prove2me | Theorems.Thm_HeteroBass_HetP_lemma_4
-- name    : HeteroBass.HetP.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:16.16198+00:00
-- url     : https://prove2.me/theorems/1b90450c-1162-43d1-bba0-6ad2ddf0b7e8
-- title:
--   Lemma 4 — two-consumer slowdown
-- statement:
--   For two consumers with nonnegative external rates $p_1\ne p_2$ and equal positive mutual influence $q$, put $\bar p=(p_1+p_2)/2$. At every positive time,
--
--   $$f^{\mathrm{het}}(t;\{p_1,p_2\},q)<f^{\mathrm{hom}}(t;\bar p,q,M=2).$$
--
--   This is the paper’s explicit two-consumer instance of the general slowdown.
--
--   **Formalization Note** The complete-graph denominator is $M-1=1$ in this case.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Lemma 4, p. 11; Appendix E, p. 27

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

namespace HeteroBass.HetP

/-- Lemma 4: the two-consumer comparison. -/
theorem lemma_4 (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hhetero : p 0 ≠ p 1) (q : ℝ) (hq : 0 < q)
    (t : ℝ) (ht : 0 < t) :
    expectedFraction p (completeQ (fun _ : Fin 2 => q)) t <
      expectedFraction (fun _ : Fin 2 => (p 0 + p 1) / 2)
        (completeQ (fun _ : Fin 2 => q)) t := by sorry

end HeteroBass.HetP
