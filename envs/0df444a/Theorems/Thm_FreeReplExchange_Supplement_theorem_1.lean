-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_1
-- name    : FreeReplExchange.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:34:04.874247+00:00
-- url     : https://prove2.me/theorems/0412bb4a-726b-4126-8b06-55cad20af2be
-- title:
--   Theorem 1 -- NIC and stability are incompatible
-- statement:
--   There is a general-utility instance with two agents and three goods on which no exchange protocol is both Nash incentive compatible and stable:
--
--   $$
--   \exists(x^{(0)},U)\;\forall M,\quad \neg\bigl(\operatorname{NIC}(M)\land\operatorname{Stable}(M)\bigr).
--   $$
--
--   Here $M$ ranges over terminating protocols satisfying the paper's standing proposal rules, and NIC and stability are the published desiderata.
--
--   Differences from the source:
--   - encoding: two agents and three goods → agents `Fin 2` and goods `Fin 3`; reason: finite index encoding with exactly the source cardinalities
--   - encoding: exchange protocol in the standing model → `IsExchangeProtocol`; reason: makes the section's termination, well-formedness, rejection, and nontrivial-proposal rules explicit without changing the protocol class
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 1, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 19 (PDF p. 21): there is a
two-agent, three-good general-utility instance on which no exchange protocol is both Nash incentive
compatible and stable.

**Formalization Note.** `Fin 2` and `Fin 3` encode the exact cardinalities.  "Exchange protocol"
includes the standing protocol rules in `IsExchangeProtocol`; NIC and stability are the published
desiderata without alteration. -/
theorem theorem_1 :
    ∃ (x0 : Fin 2 → Fin 3 → Bool) (U : Fin 2 → Fin 2 → Fin 3 → ℝ), SignCond U ∧
      ∀ M : Protocol (Fin 2) 3, IsExchangeProtocol x0 M →
        ¬ (IsNIC x0 U M ∧ IsStable x0 U M) := by sorry

end FreeReplExchange.Supplement
