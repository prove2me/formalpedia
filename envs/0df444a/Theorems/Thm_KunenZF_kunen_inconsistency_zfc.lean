-- Prove2me | Theorems.Thm_KunenZF_kunen_inconsistency_zfc
-- name    : KunenZF.kunen_inconsistency_zfc
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T16:37:58.691205+00:00
-- url     : https://prove2.me/theorems/a5398c4b-52b3-4e6c-b06c-06227a565995
-- title:
--   Kunen inconsistency in $\mathrm{ZFC}$
-- statement:
--   **Kunen's inconsistency theorem (1971), under Choice.** Adding the Axiom of Choice to the Reinhardt theory yields an inconsistent theory: $\mathrm{ZFC}(j)$ refutes the existence of a nontrivial elementary embedding $j : V \to V$. This is the classical upper bound of the large cardinal hierarchy, and the milestone that the open goal asks to extend from $\mathrm{ZFC}$ to $\mathrm{ZF}$. Kunen's proof uses Choice essentially (an $\omega$-Jónsson function argument); formalizing it is a substantial, well-defined task independent of the open goal.
--
--   **Formalization Note.** Stated as the nonexistence of a model of the Reinhardt theory union the Axiom of Choice sentence (imported from `ContinuumHypothesis.acSentence`).
-- source:
--   Kunen, Elementary embeddings and infinitary combinatorics, J. Symbolic Logic 36 (1971), 407–413, https://doi.org/10.2307/2269948; HKP Theorem 1, https://arxiv.org/abs/1106.1951.

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

universe u

open FirstOrder FirstOrder.Language

namespace KunenZF
theorem kunen_inconsistency_zfc {M : Type u} [setLangJ.Structure M] :
    ¬ (M ⊨ zfcReinhardtTheory) := by sorry
end KunenZF
