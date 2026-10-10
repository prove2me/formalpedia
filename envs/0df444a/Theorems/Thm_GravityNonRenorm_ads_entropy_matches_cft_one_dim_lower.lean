-- Prove2me | Theorems.Thm_GravityNonRenorm_ads_entropy_matches_cft_one_dim_lower
-- name    : GravityNonRenorm.ads_entropy_matches_cft_one_dim_lower
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:14.680995+00:00
-- url     : https://prove2.me/theorems/ef7e5ff0-84da-4f03-b26b-8867e2826131
-- title:
--   AdS black-hole entropy matches a $(d-1)$-dimensional CFT
-- statement:
--   Let $d\ge3$, $G_N>0$, $R_{\rm AdS}>0$ and $a,b,R>0$. Let $S_{\rm AdS}(M)$ be the Bekenstein–Hawking entropy of the $d$-dimensional Schwarzschild–AdS black hole of mass $M$ (Eq. 34), and let $S^{(d-1)}_{\rm CFT}(E)$ be the entropy-energy function (Eqs. 29–30) of a CFT in $d-1$ spacetime dimensions with data $a,b,R$. Then, as $E\to\infty$,
--
--   $$S_{\rm AdS}(E)=\Theta\bigl(S^{(d-1)}_{\rm CFT}(E)\bigr).$$
--
--   Both grow like $E^{(d-2)/(d-1)}$: AdS gravity in $d$ dimensions has the density of states of a CFT in one dimension fewer, as predicted by AdS/CFT.
-- source:
--   Assaf Shomer, A pedagogical explanation for the non-renormalizability of gravity, arXiv:0709.3555v2 [hep-th] (2007), https://arxiv.org/abs/0709.3555

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm
theorem ads_entropy_matches_cft_one_dim_lower (d : ℕ) (hd : 3 ≤ d) (G RAdS a b R : ℝ)
    (hG : 0 < G) (hRAdS : 0 < RAdS) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    (fun M : ℝ => adsBHEntropy d G M RAdS) =Θ[atTop]
      (fun E : ℝ => cftEntropyOfEnergy (d - 1) a b R E) := by sorry
end GravityNonRenorm
