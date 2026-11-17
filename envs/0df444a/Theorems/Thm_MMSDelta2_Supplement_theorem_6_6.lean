-- Prove2me | Theorems.Thm_MMSDelta2_Supplement_theorem_6_6
-- name    : MMSDelta2.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:07:38.515553+00:00
-- url     : https://prove2.me/theorems/482e5f83-9e5b-4cad-8b71-8cd814d3b58c
-- title:
--   Theorem 6.6 — MMS existence is NP-hard, even for five agents with two valuation functions
-- statement:
--   Consider additive goods instances: $n\ge 1$ agents, $m$ goods, and nonnegative rational values $v_i(g)$, given in binary. Deciding whether such an instance admits an MMS allocation is NP-hard, and remains NP-hard on instances with exactly five agents and only two distinct valuation functions:
--   $$\mathrm{MMS\text{-}Goods}\ \text{is NP-hard}\quad\text{and}\quad \mathrm{MMS\text{-}Goods}\big|_{\,n=5,\ \mathrm{numTypes}(v)\le 2}\ \text{is NP-hard},$$
--   under polynomial-time many-one reductions.
--
--   This is the paper's first hardness result, a reduction from PARTITION on the KPW core; it introduces the row-forcing structure that the $\Delta_2^P$-hardness of Theorem 1.1 refines.
--
--   **Formalization Note** The general language is the published `MMSDelta2.MMSLang`; the restricted one is `GoodsLangOn` with the class "$n=5$ and at most two distinct rows of $v$".
--
--   Differences from the source:
--   - reading: "NP-hard, even for five agents with only two distinct valuation functions" → two clauses, NP-hardness of the general problem and of the restriction to n = 5 with numTypes v ≤ 2; reason: "even for" asserts hardness of the problem and of the restricted problem, as in the base goal; "only two" is read as at most two (with one type an MMS allocation always exists, p.3, so the restricted class contains exactly the paper's two-type instances plus trivial yes-instances)
--   - encoding: an additive goods instance → its binary code instCode (base mission); non-codes are not in the language; NP languages over every finite nonempty alphabet on the Cook machines of CookPvsNP_defs; reason: Lean convention of the base mission; the paper fixes no encoding, and every reasonable one is polynomially equivalent
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorem 6.6, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MMSDelta2_MMSLang
import Definitions.Def_MMSDelta2_Supplement_NPHard
import Definitions.Def_MMSDelta2_Supplement_numTypes
import Definitions.Def_MMSDelta2_Supplement_GoodsLangOn

namespace MMSDelta2.Supplement

/-- **Theorem 6.6**, p.26 (PDF p.28).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

"Deciding whether an additive goods instance admits an MMS allocation is NP-hard, even for five
agents with only two distinct valuation functions."

**Formalization Note.** Two clauses: the general language `MMSDelta2.MMSLang` (any `n ≥ 1`) is
NP-hard, and so is its restriction to instances with exactly five agents and at most two distinct
valuation functions (`numTypes v ≤ 2`). Values are nonnegative rationals in binary; hardness is by
polynomial-time many-one reductions (`CookPvsNP_defs`) from every NP language. -/
theorem theorem_6_6 :
    NPHard MMSLang ∧ NPHard (GoodsLangOn (fun n _ v => n = 5 ∧ numTypes v ≤ 2)) := by sorry

end MMSDelta2.Supplement
