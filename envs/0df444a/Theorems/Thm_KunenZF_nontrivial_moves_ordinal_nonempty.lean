-- Prove2me | Theorems.Thm_KunenZF_nontrivial_moves_ordinal_nonempty
-- name    : KunenZF.nontrivial_moves_ordinal_nonempty
-- status  : Proved
-- author  : @teargosling
-- created : 2026-11-27T03:41:12.629301+00:00
-- url     : https://prove2.me/theorems/b0796785-6c7a-5c44-b667-39058c11cb0f
-- title:
--   A nontrivial elementary $j : V \to V$ moves an ordinal (nonempty model)
-- statement:
--   In $\mathrm{ZF}(j)$, any nontrivial elementary embedding $j : V \to V$ must move some ordinal. Equivalently, adjoining the sentence "$j$ fixes every ordinal" to `reinhardtTheory` yields an inconsistent first-order theory, so no nonempty $\{\in, j\}$-structure models `reinhardtTheory ∪ {SFormulaJ.closeJ fixesOrdinalsFormula}`. Consequently, any nontrivial elementary embedding $j : V \to V$ in a model of $\mathrm{ZF}(j)$ possesses a least moved ordinal (its critical point $\operatorname{crit}(j)$), which is a Reinhardt cardinal.
--
--   This is the critical-point existence clause of Hamkins, Kirmayer, and Perlmutter, *Generalizations of the Kunen inconsistency*, Lemma 4(2), specialized to self-embeddings of $V$, and holds in $\mathrm{ZF}(j)$ without the Axiom of Choice.
--
--   **Formalization Note:** This adds the standard first-order nonemptiness hypothesis `[Nonempty M]` missing from `KunenZF.nontrivial_moves_ordinal` (without `[Nonempty M]`, the empty structure `PEmpty.{u + 1}` vacuously satisfies every universally closed sentence `close φ` and `closeJ ψ`).
-- source:
--   Joel David Hamkins, Greg Kirmayer, and Norman Lewis Perlmutter, Generalizations of the Kunen inconsistency, Annals of Pure and Applied Logic 163 (2012), no. 12, 1872-1890, Lemma 4(2), https://arxiv.org/abs/1106.1951

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

universe u

open FirstOrder FirstOrder.Language

namespace KunenZF
theorem nontrivial_moves_ordinal_nonempty {M : Type u} [setLangJ.Structure M] [Nonempty M] :
    ¬ (M ⊨ (reinhardtTheory ∪ {SFormulaJ.closeJ fixesOrdinalsFormula})) := by sorry
end KunenZF
