-- Prove2me | Theorems.Thm_MMSDelta2_Supplement_theorem_1_5
-- name    : MMSDelta2.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:09:29.171729+00:00
-- url     : https://prove2.me/theorems/9217991f-e293-4414-8dd6-f4385b942172
-- title:
--   Theorem 1.5 (Corollary 9.2) — the hardness results extend to chores
-- statement:
--   Consider additive **chores** instances: $n\ge 1$ agents and nonpositive rational values $v_i(g)\le 0$, an MMS allocation being one with $v_i(A_i)\ge\mathrm{MMS}_i$ (equivalently $c_i(A_i)\le\min_P\max_j c_i(P_j)$ for the costs $c_i=-v_i$). Deciding whether such an instance admits an MMS allocation has the same complexity as for goods:
--
--   1. it is $\Delta_2^P$-complete, and $\Delta_2^P$-complete for exactly five agents;
--   2. it is (weakly) co-NP-hard, and co-NP-hard for exactly three agents, with values in binary;
--   3. it is strongly co-NP-hard, and strongly co-NP-hard for at most two agent types: for some $k$, the restriction to instances whose values are integers of absolute value at most $\ell^k+k$ ($\ell$ the length of the instance) is co-NP-hard, and likewise (for some $k$) with at most two agent types.
--
--   Theorem 1.5 is labelled informal in the paper; its formal statement is Corollary 9.2, obtained by a polynomial-time goods-to-chores transformation (Lemma 9.1) that preserves MMS existence, the number of agents and the number of agent types.
--
--   **Formalization Note** The languages are `ChoresLangOn` for the respective classes; $\Delta_2^P$-completeness is the base mission's `Delta2PComplete`, hardness is by polynomial-time many-one reductions, and "$k$-bounded" is `IntBounded k` as in Theorem 1.3.
--
--   Differences from the source:
--   - reading: Theorem 1.5 (Informal), "the hardness results above extend to chores" → the content of Corollary 9.2, its formal statement: Δ₂ᴾ-completeness in general and for five agents, weak co-NP-hardness in general and for three agents, strong co-NP-hardness in general and for at most two agent types; reason: Corollary 9.2 (p.46) states exactly Theorem 1.5's precise sentences, and Table 1 lists Theorems 1.1–1.3 "for both goods and chores setting"
--   - reading: weakly / strongly co-NP-hard, "even for" → as in Theorems 1.2 and 1.3 (binary values; for strong hardness, for some k, integers bounded by ℓ^k + k; general and restricted clauses; "two agent types" as at most two); reason: same definitions as the goods results the corollary transfers
--   - encoding: chores MMS allocation (costs, c_i(A_i) ≤ min max c_i(P_j)) → the base HasMMSAllocation in values on instances with nonpositive values; reason: p.12 shows the two formulations are equivalent
--   - encoding: an additive chores instance → its binary code instCode with sign bits; non-codes and instances outside the class are not in the language; reason: Lean convention of the base mission; the restricted classes are decidable in polynomial time and contain no-instances
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Theorem 1.5 (Informal), p.4 (PDF p.6); formal statement Corollary 9.2, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_MMSDelta2_Delta2P
import Definitions.Def_MMSDelta2_Supplement_NPHard
import Definitions.Def_MMSDelta2_Supplement_numTypes
import Definitions.Def_MMSDelta2_Supplement_IntBounded
import Definitions.Def_MMSDelta2_Supplement_ChoresLangOn

namespace MMSDelta2.Supplement

/-- **Theorem 1.5 (Informal)**, p.4 (PDF p.6), at the strength of its formal statement
**Corollary 9.2**, p.46 (PDF p.48).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

Theorem 1.5: "The hardness results above extend to chores. In particular, deciding whether an
additive chores instance admits an MMS allocation is Δ₂ᴾ-complete. The restricted co-NP-hardness
results for additive goods yield the corresponding hardness results for additive chores."
Corollary 9.2: "Deciding whether an additive chores instance admits an MMS allocation is
Δ₂ᴾ-complete, even for five agents. Moreover, the problem is weakly co-NP-hard even for three
agents, and strongly co-NP-hard even for two agent types."

**Formalization Note.** Chores instances have nonpositive rational values; the MMS allocation is
the base mission's `MMSDelta2.HasMMSAllocation`, which on such instances is the paper's chores MMS
allocation. Clauses: `Δ₂ᴾ`-completeness (base `Delta2PComplete`) of all chores instances and of
five-agent ones; co-NP-hardness (numbers in binary) of all chores instances and of three-agent
ones; strong co-NP-hardness (values integers bounded by `ℓ^k + k`, `ℓ` the code length, as in
Theorem 1.3) of all chores instances and of those with at most two agent types. -/
theorem theorem_1_5 :
    Delta2PComplete ChoresLang ∧ Delta2PComplete ChoresLang5 ∧
      CoNPHard ChoresLang ∧ CoNPHard ChoresLang3 ∧
      (∃ k : ℕ, CoNPHard (ChoresLangOn (IntBounded k))) ∧
      (∃ k : ℕ, CoNPHard (ChoresLangOn (fun n m v => IntBounded k n m v ∧ numTypes v ≤ 2))) := by sorry

end MMSDelta2.Supplement
