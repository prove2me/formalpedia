-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_constants_ratFunc
-- name    : LiouvilleDiffAlg.constants_ratFunc
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T17:32:04.663127+00:00
-- url     : https://prove2.me/theorems/583d47ee-ab2b-44cd-bca2-c37439b1641b
-- title:
--   $\operatorname{Con}(\mathbb{C}(x)) = \mathbb{C}$
-- statement:
--   Equip $\mathbb{C}(x)$ with the standard derivative $D = d/dx$ (any derivation with $D(p) = p'$ for all polynomials $p$). Then the constants are exactly the complex numbers:
--   $$\operatorname{Con}(\mathbb{C}(x)) = \{ r \in \mathbb{C}(x) : Dr = 0 \} = \mathbb{C}.$$
--
--   This identifies the constant field in the running example. It is the constant field that the hypothesis $\operatorname{Con}(F) = \operatorname{Con}(G)$ of Liouville's theorem refers to.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, https://en.wikipedia.org/w/index.php?title=Liouville%27s_theorem_(differential_algebra)&oldid=1349223559, section "Examples": "The constants of this field are just the complex numbers $\mathbb{C}$; that is, $\operatorname{Con}(\mathbb{C}(x)) = \mathbb{C}$"

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_RatFunc

open scoped Differential

namespace LiouvilleDiffAlg

theorem constants_ratFunc [Differential (RatFunc ℂ)] (hD : IsStandardDerivation) :
    constants (RatFunc ℂ) = Set.range (algebraMap ℂ (RatFunc ℂ)) := by sorry

end LiouvilleDiffAlg
