-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_bundleLang_mem_NP
-- name    : MultiPurchase.Hardness.bundleLang_mem_NP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:00.440898+00:00
-- url     : https://prove2.me/theorems/b82e0567-97a5-4e21-86fe-ec8b43d31e36
-- title:
--   Theorem 1, p. 17, membership half — the BundleMVL-2 decision problem is in NP
-- statement:
--   The decision version of the unconstrained BundleMVL-2 revenue optimization problem (5) — given a BundleMVL-2 instance with rational data and a rational threshold $\kappa$, is the instance well formed and is there a recommendation set $C\subseteq W$ with $R_2(C)\ge\kappa$? — belongs to the class NP:
--
--   $$\text{BundleMVL-2-DEC}\in\mathrm{NP}.$$
--
--   This is one of the two halves of the NP-completeness asserted in Theorem 1.
--
--   **Formalization Note** The language is the set of binary codes of yes-instances over the alphabet $\{0,1,-,\#\}$ (numbers in binary, rationals as reduced numerator and denominator), and NP is Cook's class (polynomial-time checking relation on a one-tape Turing machine with polynomially bounded certificates). The paper asserts membership in NP without argument.
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17 (PDF 17), Theorem 1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

open CookPvsNP ProjSchedTW.Complexity

/-- Theorem 1, p. 17, membership half: the decision version of the unconstrained BundleMVL-2
revenue problem (5) is in NP. -/
theorem bundleLang_mem_NP : bundleLang ∈ NP BSym := by sorry

end MultiPurchase.Hardness
