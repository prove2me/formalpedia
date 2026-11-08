-- Prove2me | Theorems.Thm_KhintchineTwoRegime_haagerupF_increasing
-- name    : KhintchineTwoRegime.haagerupF_increasing
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:07.058329+00:00
-- url     : https://prove2.me/theorems/f0785978-daaf-45ef-9a32-36d028316b71
-- title:
--   Haagerup's $F$ is increasing on $(0,\infty)$ and $F(4)=3/4$
-- statement:
--   Haagerup's function
--   $$
--   F(s)=\frac{2}{\sqrt{\pi s}}\,\frac{\Gamma((s+1)/2)}{\Gamma(s/2)},\qquad s>0,
--   $$
--   is (strictly) increasing on $(0,\infty)$, and
--   $$
--   F(4)=\frac34.
--   $$
--   The paper cites both facts (§2.2) and uses them in the proof of Corollary 1: coordinates at most $1/2$ have $\omega_i^{-2}\ge4$, so each contributes at least $\tfrac34\omega_i^2$ to Haagerup's lower bound.
--
--   Differences from the source:
--   - reading: F is increasing → F is strictly increasing on (0, ∞) (StrictMonoOn); reason: the stronger of the two readings; F is strictly increasing there
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2.2, p.6 (properties of F stated after eq. (8))

import Mathlib
import Definitions.Def_KhintchineTwoRegime_haagerupF

namespace KhintchineTwoRegime

/-- Haagerup's function `F` of (8) is increasing on `(0, ∞)` and satisfies `F(4) = 3/4`
(cited in Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §2.2, p.6).

**Formalization Note** "Increasing" is read as strictly increasing on `s > 0` (the stronger
reading; `F` is strictly increasing there). -/
theorem haagerupF_increasing :
    StrictMonoOn haagerupF (Set.Ioi 0) ∧ haagerupF 4 = 3 / 4 := by sorry

end KhintchineTwoRegime
