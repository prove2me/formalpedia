-- Prove2me | Theorems.Thm_OmniMix_closed_forms_bv_dv
-- name    : OmniMix.closed_forms_bv_dv
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T01:40:47.563205+00:00
-- url     : https://prove2.me/theorems/583e6284-707a-4e9e-8e32-42271e3a0717
-- title:
--   §2, p.10 — closed forms of $b_v$ and $d_v$ for the V-shaped loss
-- statement:
--   Let $v\in[0,1]$. The V-shaped loss $\lambda_v$ is proper, so its post-processing map is the identity, and for all $p,q\in[0,1]$ its test function and properness gain are
--   $$
--   b_{\lambda_v}(p,q)=\mathbb I\{p<v\le q\}-\mathbb I\{q<v\le p\},\qquad d_{\lambda_v}(p,q)=|v-p|\,b_{\lambda_v}(p,q)^2,
--   $$
--   where $b_\ell(p,q)=\Delta_\ell(p)-\Delta_\ell(q)$, $\Delta_\ell(q)=\ell(q,1)-\ell(q,0)$, and $d_\ell(p,q)=\mathbb E_{Y\sim\mathrm{Ber}(p)}[\ell(q,Y)-\ell(p,Y)]$.
--
--   These closed forms are the shorthands $b_v,d_v$ used in every later regret identity.
--
--   Differences from the source:
--   - generalization: the closed forms of b_v and d_v → also the conjunct that λ_v is proper; reason: properness is what makes the §2 convention π_{λ_v} = id apply; dropping the conjunct gives the page's claim
--   - encoding: b_v, d_v as real numbers → the general b_ℓ, d_ℓ (computed in ℝ∪{±∞}) equal the real closed forms; reason: λ_v is real-valued, so nothing is lost
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.10 (PDF p.12), closed forms of b_v and d_v

import Mathlib
import Definitions.Def_OmniMix_IsProper
import Definitions.Def_OmniMix_vLoss
import Definitions.Def_OmniMix_bTest
import Definitions.Def_OmniMix_dGain
import Definitions.Def_OmniMix_bV
import Definitions.Def_OmniMix_dV

namespace OmniMix

/-- **Closed forms of `b_v` and `d_v` (§2, p.10).** Liu–Luo–Ratliff, arXiv:2610.41023, §2, p.10: "For a V-shaped loss `λ_v`, we use
`b_v(p, q)` and `d_v(p, q)` as the shorthands for `b_{λ_v}(p, q)` and `d_{λ_v}(p, q)`. It is
straightforward to verify that they take the following simple forms:
`b_v(p, q) = I{p < v ≤ q} − I{q < v ≤ p}` and `d_v(p, q) = |v − p|b_v(p, q)²`."

For every threshold `v ∈ [0,1]`, `λ_v` is proper (so `π_{λ_v} = id`), and its test function and
properness gain, from the general definitions of p.9, have these closed forms. -/
theorem closed_forms_bv_dv (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    IsProper (vLoss v) ∧ ∀ p q : unitInterval,
      bTest (vLoss v) p q = ((bV v p q : ℝ) : EReal) ∧
        dGain (vLoss v) p q = ((dV v p q : ℝ) : EReal) := by sorry

end OmniMix
