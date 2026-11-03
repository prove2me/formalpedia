-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_canon_filter_polytime
-- name    : MultiPurchase.Hardness.canon_filter_polytime
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T03:52:58.505773+00:00
-- url     : https://prove2.me/theorems/328c29bb-ac27-4509-8686-1e4514b7afdf
-- title:
--   BundleMVL-2 NP checker, step 2: checking that all rationals are in lowest terms is polynomial-time
-- statement:
--   With the notation of `Definitions.Def_MultiPurchase_Hardness_Checker` (checker inputs $\langle c\#d\rangle$ and the condition $\mathrm{ShapeOK}$), there is a function $g$ on checker inputs that is computable in polynomial time by a Cook Turing machine, maps the empty word to the empty word, and satisfies, for every $c, d$ with $\mathrm{ShapeOK}(c,d)$,
--   $$g(\langle c\#d\rangle) = \begin{cases} \langle c\#d\rangle & \text{if } \mathrm{CanonOK}(c),\\ \varepsilon & \text{otherwise,}\end{cases}$$
--   where $\mathrm{CanonOK}(c)$ says that for each of the $2n + n(n-1)/2 + 2$ rationals $(\mathrm{num}_t, \mathrm{den}_t)$ encoded in $c$ one has $\mathrm{den}_t > 0$ and $\gcd(\mathrm{num}_t, \mathrm{den}_t) = 1$.
--
--   This is the second check of the BundleMVL-2 verifier: instance codes write every rational as its normalized numerator and denominator, so a word is a code only if every pair is in lowest terms. The check amounts to polynomially many gcd computations on binary numbers.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17, Theorem 1 (membership half: the decision version of (5) is in NP), eq. (4); polynomial-time computability as in S. Cook, The P versus NP problem (Clay Mathematics Institute), §1 and Definition 3

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Definitions.Def_MultiPurchase_Hardness_Checker

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

open Classical in
theorem canon_filter_polytime :
    ∃ g : List (Option (BSym ⊕ Bool)) → List (Option (BSym ⊕ Bool)),
      PolyTimeComputable g ∧ g [] = [] ∧
        ∀ c d, ShapeOK c d → g (chkWord c d) = if CanonOK c then chkWord c d else [] := by sorry

end MultiPurchase.Hardness
