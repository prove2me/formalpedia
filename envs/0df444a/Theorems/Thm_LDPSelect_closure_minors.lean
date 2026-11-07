-- Prove2me | Theorems.Thm_LDPSelect_closure_minors
-- name    : LDPSelect.closure_minors
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:04.27924+00:00
-- url     : https://prove2.me/theorems/9ca9c050-575a-47ed-8efb-47ea0876ad7f
-- title:
--   A.7, closure — the class $\mathcal G$ is closed under minors
-- statement:
--   Let $\mathcal F$ be a downward-closed family in the class $\mathcal G$ of Theorem 1. Every minor of $\mathcal F$ is in $\mathcal G$.
--
--   Differences from the source:
--   - encoding: minors by repeated contraction and deletion, up to isomorphism → one contraction of a feasible set followed by one deletion, with an injective relabelling; reason: the paper's own reduction (§3.4, p.8): (F∖D)/I = (F/I)∖D
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), A.7, Closure, pp.19–20 (pdf pp.20–21)

import Mathlib
import Definitions.Def_LDPSelect_InClass
import Definitions.Def_LDPSelect_IsMinorOf

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), A.7, pp.19–20, Closure.

The class `G` is closed under minors. -/
theorem closure_minors {k n : ℕ} (F : Family n) (hF : IsDownClosed F) (hG : InClass F)
    (O : Family k) (hO : IsMinorOf O F) : InClass O := by sorry

end LDPSelect
