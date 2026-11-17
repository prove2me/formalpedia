-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_5
-- name    : FreeReplExchange.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:36:58.066203+00:00
-- url     : https://prove2.me/theorems/da19c3ed-0e3c-4b18-af02-f55275156cf3
-- title:
--   Theorem 5 -- truthful holdings reporting is not a Nash equilibrium
-- statement:
--   Suppose utilities are reported truthfully and every agent follows the accepting policy. For every stable MIC reporting mechanism, there is an ESC instance with three agents and two goods on which truthful reporting of initial holdings is not a Nash equilibrium.
--
--   A legal deviation may hide truly owned goods but cannot fabricate goods. MIC and stability are evaluated on the report, whereas realized holdings begin from the true allocation and a hidden-good duplicate still counts once.
--
--   Differences from the source:
--   - encoding: three agents and two goods → agents `Fin 3` and goods `Fin 2`; reason: finite index encoding with exactly the source cardinalities
--   - encoding: a protocol designed from reported instance data → `ReportingMechanism`, a family indexed by reported holdings and truthful utilities; reason: exposes the report-to-protocol dependence required by the source game
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 5, p.25 (PDF p.27), reporting model pp.24--25 (PDF pp.26--27)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_ReportingMechanism

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 5, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 25 (PDF p. 27): for every
stable MIC reporting mechanism there is a three-agent, two-good ESC instance on which truthful
reporting of initial holdings is not a Nash equilibrium when utilities are truthful and all agents
accept.

**Formalization Note.** A unilateral report may hide any truly owned goods and cannot fabricate
goods.  The protocol properties use the report, while realized holdings and payoff use the truth. -/
theorem theorem_5 :
    ∀ F : ReportingMechanism (Fin 3) 2, IsStableMICReportingMechanism F →
      ∃ (y0 : Fin 3 → Fin 2 → Bool) (U : Fin 3 → Fin 3 → Fin 2 → ℝ)
          (β : Fin 3 → Fin 3 → ℝ),
        IsESC U β ∧ ¬ TruthfulHoldingsReportingNE y0 U F := by sorry

end FreeReplExchange.Supplement
