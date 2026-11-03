-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_rev_check_polytime
-- name    : MultiPurchase.Hardness.rev_check_polytime
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T03:52:49.102005+00:00
-- url     : https://prove2.me/theorems/b2ba0e37-2e5b-4782-a658-73d89d1c0241
-- title:
--   BundleMVL-2 NP checker, step 3: checking $R_2(C) \ge \kappa$ for a certified set $C$ is polynomial-time
-- statement:
--   With the notation of `Definitions.Def_MultiPurchase_Hardness_Checker`, there is a function $g$ on checker inputs that is computable in polynomial time by a Cook Turing machine, maps the empty word to the empty word, and satisfies, for every $c, d$ with $\mathrm{ShapeOK}(c,d)$ and $\mathrm{CanonOK}(c)$,
--   $$g(\langle c\#d\rangle) \ne \varepsilon \iff \mathrm{RevOK}(c,d).$$
--   Here, reading the rationals $r_i, V_{\{i\}}, V_{\{i,j\}}, v_0, \kappa$ from $c$ and $x_i = d_i \in \{0,1\}$, $\mathrm{RevOK}(c,d)$ is the inequality
--   $$\kappa\Big(v_0 + \sum_{i} x_i V_{\{i\}} + \sum_{i<j} x_i x_j V_{\{i,j\}}\Big) \le \sum_i x_i\, r_i V_{\{i\}} + \sum_{i<j} x_i x_j (r_i + r_j) V_{\{i,j\}},$$
--   i.e. $R_2(C) \ge \kappa$ (eq. (4), p. 17) for the recommendation set $C = \{i : x_i = 1\}$, since the denominator of $R_2(C)$ is positive.
--
--   This is the arithmetic core of the NP verifier for the BundleMVL-2 decision problem: given the guessed set $C$, the expected revenue $R_2(C)$ is a ratio of sums of products of the input rationals, and comparing it with $\kappa$ takes polynomially many additions and multiplications of binary numbers whose lengths stay polynomial in the input length.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17, Theorem 1 (membership half: the decision version of (5) is in NP), eq. (4); polynomial-time computability as in S. Cook, The P versus NP problem (Clay Mathematics Institute), §1 and Definition 3

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Definitions.Def_MultiPurchase_Hardness_Checker

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

theorem rev_check_polytime :
    ∃ g : List (Option (BSym ⊕ Bool)) → List (Option (BSym ⊕ Bool)),
      PolyTimeComputable g ∧ g [] = [] ∧
        ∀ c d, ShapeOK c d → CanonOK c → (g (chkWord c d) ≠ [] ↔ RevOK c d) := by sorry

end MultiPurchase.Hardness
