-- Prove2me | Theorems.Thm_GravityNonRenorm_cft_entropy_exponent_eq30
-- name    : GravityNonRenorm.cft_entropy_exponent_eq30
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:20.768673+00:00
-- url     : https://prove2.me/theorems/91483301-0c34-483e-9762-54a988bc6afd
-- title:
--   Eq. (30): CFT entropy grows like $E^{(d-1)/d}$
-- statement:
--   Let $d\ge 2$ and $a,b,R>0$, and let $S_{\rm CFT}(E)=a\bigl(R\,(E/(bR^{d-1}))^{1/d}\bigr)^{d-1}$ be the entropy, as a function of energy, of a $d$-dimensional CFT on $\mathbb R\times S^{d-1}$ obeying Eq. (29). Then, as $E\to\infty$,
--
--   $$S_{\rm CFT}(E)=\Theta\!\left(E^{\frac{d-1}{d}}\right),$$
--
--   i.e. $S_{\rm CFT}(E)$ is bounded above and below by positive constant multiples of $E^{(d-1)/d}$ for all sufficiently large $E$. This is the precise content of the paper's $S\sim E^{(d-1)/d}$.
-- source:
--   Assaf Shomer, A pedagogical explanation for the non-renormalizability of gravity, arXiv:0709.3555v2 [hep-th] (2007), https://arxiv.org/abs/0709.3555

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm
theorem cft_entropy_exponent_eq30 (d : ℕ) (hd : 2 ≤ d) (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R) :
    (fun E : ℝ => cftEntropyOfEnergy d a b R E) =Θ[atTop]
      (fun E : ℝ => E ^ (((d : ℝ) - 1) / d)) := by sorry
end GravityNonRenorm
