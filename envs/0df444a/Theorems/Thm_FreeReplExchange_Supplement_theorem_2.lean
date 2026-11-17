-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_2
-- name    : FreeReplExchange.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:34:35.222024+00:00
-- url     : https://prove2.me/theorems/e9624b35-3cd7-4d5e-911d-e90be921c115
-- title:
--   Theorem 2 -- DSIC and stability are incompatible under ESC
-- statement:
--   There is an ESC instance with four agents and two goods on which no exchange protocol is both dominant-strategy incentive compatible and stable:
--
--   $$
--   \exists(x^{(0)},U,\beta)\;\forall M,\quad \neg\bigl(\operatorname{DSIC}(M)\land\operatorname{Stable}(M)\bigr).
--   $$
--
--   DSIC quantifies over arbitrary strategy profiles of the other agents; it is not the Nash condition in which the others accept everything.
--
--   Differences from the source:
--   - encoding: four agents and two goods → agents `Fin 4` and goods `Fin 2`; reason: finite index encoding with exactly the source cardinalities
--   - encoding: exchange protocol in the standing model → `IsExchangeProtocol`; reason: makes the standing protocol rules explicit without changing the protocol class
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 2, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 20 (PDF p. 22): there is a
four-agent, two-good ESC instance on which no exchange protocol is both dominant-strategy
incentive compatible and stable.

**Formalization Note.** DSIC quantifies over arbitrary strategies of all other agents, not merely
their accepting policies. -/
theorem theorem_2 :
    ∃ (x0 : Fin 4 → Fin 2 → Bool) (U : Fin 4 → Fin 4 → Fin 2 → ℝ)
        (β : Fin 4 → Fin 4 → ℝ), IsESC U β ∧
      ∀ M : Protocol (Fin 4) 2, IsExchangeProtocol x0 M →
        ¬ (IsDSIC x0 U M ∧ IsStable x0 U M) := by sorry

end FreeReplExchange.Supplement
