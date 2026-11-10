-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_D_3
-- name    : HoneycombCodes.lemma_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:41.763133+00:00
-- url     : https://prove2.me/theorems/e432fd23-a9fe-419a-a9ff-75a4bd7e08d6
-- title:
--   Lemma D.3 — an entropy order for $g$
-- statement:
--   Let $a,b,c,d\in[0,1]$. If
--
--   $$
--   \max\{a,b\}\le\max\{c,d\},\qquad ab\le cd,
--   $$
--
--   then $g(a)+g(b)\le g(c)+g(d)$.
--
--   This elementary inequality isolates the range in which the constant-weight bridge of Lemma D.5 is valid.
--
--   Differences from the source: none.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.3, Lemma D.3, p.61 (PDF 63)

import Mathlib
import Definitions.Def_HoneycombCodes_H2

set_option autoImplicit false

namespace HoneycombCodes

/-- **Lemma D.3**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.3, p.61 (PDF 63). Let `a, b, c, d ∈ [0, 1]`. If
`max{a, b} ≤ max{c, d}` and `ab ≤ cd`, then `g(a) + g(b) ≤ g(c) + g(d)`. -/
theorem lemma_D_3 (a b c d : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (hmax : max a b ≤ max c d) (hprod : a * b ≤ c * d) :
    g a + g b ≤ g c + g d := by sorry

end HoneycombCodes
