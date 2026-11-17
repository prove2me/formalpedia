-- Prove2me | Theorems.Thm_MMSDelta2_Supplement_theorem_1_2
-- name    : MMSDelta2.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:08:09.540972+00:00
-- url     : https://prove2.me/theorems/dfd14979-6856-4c56-bf6d-e9a6c09a4a22
-- title:
--   Theorem 1.2 — MMS existence is weakly co-NP-hard, even for three agents
-- statement:
--   Consider additive goods instances with $n\ge 1$ agents and nonnegative rational values given in binary. Deciding whether such an instance admits an MMS allocation is co-NP-hard, and remains co-NP-hard on instances with exactly three agents:
--   $$\mathrm{MMS\text{-}Goods}\ \text{is co-NP-hard}\quad\text{and}\quad \mathrm{MMS\text{-}Goods}\big|_{\,n=3}\ \text{is co-NP-hard},$$
--   under polynomial-time many-one reductions. "Weakly" means that the numbers are encoded in binary, with no bound on their size.
--
--   With two agents an MMS allocation always exists for additive valuations, so three agents is the first case with a hardness result.
--
--   **Formalization Note** The general language is the published `MMSDelta2.MMSLang`; the restricted one is `GoodsLangOn` with the class $n=3$.
--
--   Differences from the source:
--   - reading: "weakly co-NP-hard, even for three agents" → two clauses, co-NP-hardness of the general problem and of the restriction to n = 3, with values in binary and unbounded; reason: "weakly" is co-NP-hardness under the binary encoding (p.3 contrasts it with hardness for unary values); "even for" asserts hardness of the problem and of the restricted problem
--   - encoding: an additive goods instance → its binary code instCode (base mission); non-codes are not in the language; coNP languages over every finite nonempty alphabet on the Cook machines of CookPvsNP_defs; reason: Lean convention of the base mission; the paper fixes no encoding, and every reasonable binary one is polynomially equivalent
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorem 1.2, p.40 (PDF p.42); also p.3 (PDF p.5)

import Mathlib
import Definitions.Def_MMSDelta2_MMSLang
import Definitions.Def_MMSDelta2_Supplement_NPHard
import Definitions.Def_MMSDelta2_Supplement_GoodsLangOn

namespace MMSDelta2.Supplement

/-- **Theorem 1.2**, p.40 (PDF p.42); also stated on p.3 (PDF p.5).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

"Deciding whether an additive goods instance admits an MMS allocation is weakly co-NP-hard, even
for three agents."

**Formalization Note.** "Weakly": co-NP-hardness with the numbers in binary (the base mission's
`instCode`), with no bound on their size. Two clauses: the general language `MMSDelta2.MMSLang`
is co-NP-hard, and so is its restriction to exactly three agents. -/
theorem theorem_1_2 :
    CoNPHard MMSLang ∧ CoNPHard (GoodsLangOn (fun n _ _ => n = 3)) := by sorry

end MMSDelta2.Supplement
