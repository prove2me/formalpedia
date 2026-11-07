-- Prove2me | Theorems.Thm_HeilmanMax3Cut_lemma_9_3
-- name    : HeilmanMax3Cut.lemma_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:32.446354+00:00
-- url     : https://prove2.me/theorems/11fb6023-dd05-49c2-b62b-7363df987494
-- title:
--   Lemma 9.3 — uniform eigenvalue bound
-- statement:
--   For every $\sigma\in[1/43,1/2]$,
--
--   $$h_{\mathrm{upper}}(\sigma)<1.967<2,\qquad h_{\mathrm{lower}}(\sigma)<0.824<2 .$$
--
--   With Lemma 9.1 these bounds make the quadratic form (132) nonnegative. The paper's proof is a computer certificate with interval arithmetic (plur_cert.py).
--
--   Differences from the source:
--   - encoding: h_upper(σ) < 1.967 < 2, h_lower(σ) < 0.824 < 2 → hUpper σ < 1.967 ∧ hLower σ < 0.824 in [0, ∞]; reason: 1.967 < 2 and 0.824 < 2 are arithmetic; the h < 2 clauses follow
--   - encoding: h_upper, h_lower of (111)–(112), real square roots of double integrals → hUpper, hLower in [0, ∞]: lower Lebesgue integrals of ENNReal.ofReal(L²/(J_*(t)J_*(s))) raised to 1/2; reason: the integrand is nonnegative, so the lintegral is the paper's integral, and a non-integrable square gives ∞ instead of a junk 0
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Lemma 9.3, Eq. (124), p.34

import Mathlib
import Definitions.Def_HeilmanMax3Cut_hLower
import Definitions.Def_HeilmanMax3Cut_hUpper

namespace HeilmanMax3Cut

/-- **Lemma 9.3 (Uniform Eigenvalue Bound).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Lemma 9.3, Eq. (124), p.34: "Uniformly for all
`σ ∈ [1/43, 1/2]`, we have `h_upper(σ) < 1.967 < 2`, `h_lower(σ) < 0.824 < 2`."

**Formalization Note.** `h_upper, h_lower ∈ [0, ∞]` (lower Lebesgue integrals), compared with the
reals `1.967` and `0.824`; the strict bounds also say they are finite. The clauses `1.967 < 2` and
`0.824 < 2` are arithmetic and not restated. The paper's proof is a computer certificate
(`plur_cert.py`). -/
theorem lemma_9_3 :
    ∀ σ ∈ Set.Icc (1 / 43 : ℝ) (1 / 2),
      hUpper σ < ENNReal.ofReal 1.967 ∧ hLower σ < ENNReal.ofReal 0.824 := by sorry

end HeilmanMax3Cut
