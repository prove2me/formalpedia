-- Prove2me | Theorems.Thm_HeteroBass_HetP_lemma_5
-- name    : HeteroBass.HetP.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:07.752145+00:00
-- url     : https://prove2.me/theorems/4af53887-58c8-46a9-9e35-ec7dd8faa59a
-- title:
--   Lemma 5 — inter-adoption CDF dominance
-- statement:
--   On a complete graph, let $p_i\ge0$ and $q_i>0$ be ordered in the same direction, with some variation in $p$ or $q$ and $\sum_i p_i>0$. Compare this network with one whose external and incoming-influence rates are their respective means. If $F_k(\tau)$ is the CDF of waiting time $k$, then
--
--   $$F_1^{\mathrm{het}}(\tau)=F_1^{\mathrm{hom}}(\tau)\quad(\tau\ge0),\qquad F_k^{\mathrm{het}}(\tau)<F_k^{\mathrm{hom}}(\tau)\quad(2\le k\le M,\;\tau>0).$$
--
--   This supplies the stagewise comparison used for the paper’s diffusion result.
--
--   **Formalization Note** Lean stage $k$ denotes the paper’s stage $k+1$. The variation and positive initial total rate are explicit because the displayed strict inequality fails without them.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Lemma 5, eq. (36), p. 11; Appendix F, pp. 28–30

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

namespace HeteroBass.HetP

/-- Lemma 5: inter-adoption holding-time CDF dominance on a complete graph. -/
theorem lemma_5 (M : ℕ) (p q : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpmono : Monotone p) (hqmono : Monotone q)
    (hhetero : (∃ i j, p i ≠ p j) ∨ (∃ i j, q i ≠ q j))
    (hseed : 0 < ∑ i, p i) :
    (∀ k : Fin M, k.val = 0 → ∀ tau : ℝ, 0 ≤ tau →
      interCDF p (completeQ q) k tau =
        interCDF (fun _ : Fin M => mean p) (completeQ (fun _ : Fin M => mean q)) k tau) ∧
    (∀ k : Fin M, 0 < k.val → ∀ tau : ℝ, 0 < tau →
      interCDF p (completeQ q) k tau <
        interCDF (fun _ : Fin M => mean p) (completeQ (fun _ : Fin M => mean q)) k tau) := by sorry

end HeteroBass.HetP
