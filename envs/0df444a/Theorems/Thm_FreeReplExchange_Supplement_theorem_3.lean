-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_3
-- name    : FreeReplExchange.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:35:25.158086+00:00
-- url     : https://prove2.me/theorems/d0f52cc4-93d7-4cef-b212-c8ca5ffc0ca5
-- title:
--   Theorem 3 -- IR and efficiency are incompatible
-- statement:
--   There is a general-utility instance with five agents and two goods on which no exchange protocol satisfies individual rationality and efficiency simultaneously:
--
--   $$
--   \exists(x^{(0)},U)\;\forall M,\quad \neg\bigl(\operatorname{IR}(M)\land\operatorname{Efficient}(M)\bigr).
--   $$
--
--   Efficiency is the published desideratum and therefore includes MIC. Individual rationality compares an agent's accept-all utility when she participates with her utility from the exchanges conducted in her absence.
--
--   Differences from the source:
--   - encoding: five agents and two goods → agents `Fin 5` and goods `Fin 2`; reason: finite index encoding with exactly the source cardinalities
--   - encoding: exchange protocol in the standing model → `IsExchangeProtocol`; reason: makes the standing protocol rules explicit without changing the protocol class
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 3, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_IsExchangeProtocol

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 3, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 23 (PDF p. 25): there is a
five-agent, two-good general-utility instance on which no exchange protocol satisfies individual
rationality and efficiency simultaneously.

**Formalization Note.** The published `IsEfficient` includes MIC, exactly as Desideratum 6 does;
`IsIR` is the participation-comparison notion, not comparison with the initial allocation. -/
theorem theorem_3 :
    ∃ (x0 : Fin 5 → Fin 2 → Bool) (U : Fin 5 → Fin 5 → Fin 2 → ℝ), SignCond U ∧
      ∀ M : Protocol (Fin 5) 2, IsExchangeProtocol x0 M →
        ¬ (IsIR x0 U M ∧ IsEfficient x0 U M) := by sorry

end FreeReplExchange.Supplement
