-- Prove2me | Theorems.Thm_KunenZF_kunen_inconsistency_zf
-- name    : KunenZF.kunen_inconsistency_zf
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T16:36:53.815196+00:00
-- url     : https://prove2.me/theorems/1deb2a22-5489-4f56-ac2d-a981c1ae996f
-- title:
--   Kunen inconsistency in $\mathrm{ZF}$ (open goal)
-- statement:
--   This is the central open problem: **does $\mathrm{ZF}$ set theory refute the existence of Reinhardt cardinals?** It asserts that no structure $(M, \in, j)$ models the Reinhardt theory $\mathrm{ZF}(j) + \mathrm{Elem}(j) + \exists x\, j(x)\ne x$, i.e. $\mathrm{ZF}$ with a unary function symbol $j$, Separation and Collection for all $\{\in,j\}$-formulas, the elementarity scheme for $j$ over pure $\in$-formulas, and the assertion that $j$ moves some set. Equivalently (by soundness and completeness), this first-order theory is inconsistent. A Reinhardt cardinal is the critical point of such a $j$; in $\mathrm{ZF}(j)$ nontriviality is equivalent to the existence of a critical point, so the statement is exactly that $\mathrm{ZF}$ refutes Reinhardt cardinals.
--
--   The problem is open: Kunen refuted the statement under Choice (1971) and Suzuki refuted the parameter-definable case in $\mathrm{ZF}$ (1999), but no proof or model in $\mathrm{ZF}$ alone is known. A **disproof** of this goal would exhibit a model of the theory — a consistency result for choiceless large cardinals.
--
--   **Formalization Note.** Stated semantically and universe-polymorphically: for every type $M$ with a $\{\in,j\}$-structure, $M$ is not a model of the theory. This is equivalent to syntactic inconsistency by Gödel's completeness theorem.
-- source:
--   Wikipedia, Reinhardt cardinal, 'Consistency in ZF' (unsolved problem: Does ZF set theory refute the existence of Reinhardt cardinals?); https://en.wikipedia.org/wiki/Reinhardt_cardinal. Formulation per HKP §1, https://arxiv.org/abs/1106.1951.

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_CH_SetTheoryLanguage

universe u

open FirstOrder FirstOrder.Language

namespace KunenZF
theorem kunen_inconsistency_zf {M : Type u} [setLangJ.Structure M] :
    ¬ (M ⊨ reinhardtTheory) := by sorry
end KunenZF
