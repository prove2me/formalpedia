-- Prove2me | Theorems.Thm_GravityNonRenorm_ads_entropy_not_cft
-- name    : GravityNonRenorm.ads_entropy_not_cft
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:11.718303+00:00
-- url     : https://prove2.me/theorems/e89d5b7f-2a2b-40fe-b629-2ded7f08fd50
-- title:
--   AdS black-hole entropy is not that of a $d$-dimensional CFT
-- statement:
--   Let $d\ge3$, $G_N>0$, $R_{\rm AdS}>0$, and let $a,b,R>0$ be the data of a $d$-dimensional CFT on $\mathbb R\times S^{d-1}$ as in Eq. (29). Let $S_{\rm AdS}(M)$ be the Bekenstein–Hawking entropy of the $d$-dimensional Schwarzschild–AdS black hole of mass $M$ (Eq. 34) and $S_{\rm CFT}(E)$ the CFT entropy as a function of energy (Eq. 30). Then it is **not** the case that
--
--   $$S_{\rm AdS}(E)=\Theta\bigl(S_{\rm CFT}(E)\bigr)\qquad(E\to\infty).$$
--
--   So the high-energy density of states of $d$-dimensional AdS gravity is not that of any $d$-dimensional CFT of the form (29).
-- source:
--   Assaf Shomer, A pedagogical explanation for the non-renormalizability of gravity, arXiv:0709.3555v2 [hep-th] (2007), https://arxiv.org/abs/0709.3555

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm
theorem ads_entropy_not_cft (d : ℕ) (hd : 3 ≤ d) (G RAdS a b R : ℝ) (hG : 0 < G)
    (hRAdS : 0 < RAdS) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    ¬ (fun M : ℝ => adsBHEntropy d G M RAdS) =Θ[atTop]
      (fun E : ℝ => cftEntropyOfEnergy d a b R E) := by sorry
end GravityNonRenorm
