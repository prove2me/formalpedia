-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_6
-- name    : FreeReplExchange.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:37:43.931746+00:00
-- url     : https://prove2.me/theorems/22d1ecec-eef2-48d5-9b4c-4400391dc397
-- title:
--   Theorem 6 -- truthful utility reporting is not a Nash equilibrium
-- statement:
--   Suppose initial holdings are reported truthfully and every agent follows the accepting policy. For every stable MIC reporting mechanism, there is a general-utility instance on which truthful reporting of utility matrices is not a Nash equilibrium.
--
--   A deviator may change every entry of her reported utility row while remaining within the model bounds. The protocol, MIC, and stability use the reported matrices, while payoff uses the true matrices.
--
--   Differences from the source:
--   - encoding: an unspecified finite witness instance → the paper's explicit witness size, agents `Fin 3` and goods `Fin 2`; reason: the existential claim is unchanged because the source proof supplies exactly this witness
--   - encoding: a protocol designed from reported instance data → `ReportingMechanism`, a family indexed by truthful holdings and reported utilities; reason: exposes the report-to-protocol dependence required by the source game
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 6, p.25 (PDF p.27), proof p.26 (PDF p.28)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_ReportingMechanism

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 6, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 25 (PDF p. 27): for every
stable MIC reporting mechanism there is a general-utility instance on which truthful reporting of
utility matrices is not a Nash equilibrium when holdings are truthful and all agents accept.

**Formalization Note.** The paper's explicit witness has three agents and two goods.  A deviator may
replace her entire utility row by any row that leaves the combined reported family within the
model's entry bounds.  Payoff is always evaluated using the true family. -/
theorem theorem_6 :
    ∀ F : ReportingMechanism (Fin 3) 2, IsStableMICReportingMechanism F →
      ∃ (x0 : Fin 3 → Fin 2 → Bool) (V : Fin 3 → Fin 3 → Fin 2 → ℝ),
        SignCond V ∧ ¬ TruthfulUtilityReportingNE x0 V F := by sorry

end FreeReplExchange.Supplement
