-- Prove2me | Theorems.Thm_KunenZF_nontrivial_moves_ordinal
-- name    : KunenZF.nontrivial_moves_ordinal
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T16:37:35.737536+00:00
-- url     : https://prove2.me/theorems/36b8ebf2-eb1f-4f04-8667-9af15b50b1f8
-- title:
--   A nontrivial elementary $j:V\to V$ moves an ordinal
-- statement:
--   In $\mathrm{ZF}(j)$, a nontrivial elementary embedding $j : V \to V$ must move an ordinal. Equivalently, adding the sentence "$j$ fixes every ordinal" to the Reinhardt theory yields an inconsistent theory. Consequently a nontrivial such $j$ has a **critical point** — the least ordinal it moves — which is a Reinhardt cardinal; this justifies reading the goal as a statement about Reinhardt cardinals rather than merely about nontrivial embeddings. This is the critical-point existence lemma of Hamkins–Kirmayer–Perlmutter (Lemma 4(2)), specialized to self-embeddings of $V$, and is provable in $\mathrm{ZF}(j)$ without Choice.
--
--   **Formalization Note.** Stated as the nonexistence of a model of the Reinhardt theory together with the universal sentence $\forall \alpha\,(\mathrm{Ordinal}(\alpha) \to j(\alpha)=\alpha)$, where "ordinal" is a transitive set of transitive sets.
-- source:
--   Hamkins–Kirmayer–Perlmutter, Generalizations of the Kunen inconsistency, Lemma 4(2) (critical point), https://arxiv.org/abs/1106.1951; Ann. Pure Appl. Logic 163 (2012), 1872–1890.

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

universe u

open FirstOrder FirstOrder.Language

namespace KunenZF
theorem nontrivial_moves_ordinal {M : Type u} [setLangJ.Structure M] :
    ¬ (M ⊨ (reinhardtTheory ∪ {SFormulaJ.closeJ fixesOrdinalsFormula})) := by sorry
end KunenZF
