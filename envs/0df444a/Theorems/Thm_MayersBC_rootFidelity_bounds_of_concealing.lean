-- Prove2me | Theorems.Thm_MayersBC_rootFidelity_bounds_of_concealing
-- name    : MayersBC.rootFidelity_bounds_of_concealing
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:25.800203+00:00
-- url     : https://prove2.me/theorems/6600ec1c-ba8f-4266-815e-b485bec0bf15
-- title:
--   Section d, p.8 — Bob's criterion gives $1 \ge F \ge 1 - 2\varepsilon$
-- statement:
--   Let $\rho_0, \rho_1$ be density matrices satisfying Bob's criterion with parameter $\varepsilon$: every binary guess has $|\mathrm{PE} - \tfrac12| \le \varepsilon$. Then the fidelity $F = \operatorname{Tr}\sqrt{\sqrt{\rho_0}\,\rho_1\sqrt{\rho_0}}$ satisfies
--
--   $$
--   1 \ge F(\rho_0, \rho_1) \ge 1 - 2\varepsilon .
--   $$
--
--   This is the point where security against Bob turns into closeness of the two commitment states.
--
--   Differences from the source:
--   - reading: Bob's best guess X satisfies |PE − 1/2| ≤ ε → IsConcealing ε ρ0 ρ1: every binary guess {Q, I − Q} satisfies |PE − 1/2| ≤ ε; reason: a guess from any measurement is a binary measurement; the best guess has PE ≤ 1/2 and swapping Q with I − Q maps PE to 1 − PE, so the two conditions are equivalent
--   - generalization: ε = 1/25 → any real ε; reason: the argument uses no property of the value 1/25
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_MayersBC_IsConcealing
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.8: "Therefore, we have BW ≥ (1 − 2ε).
Furthermore, in [7,18] it is shown that the minimum of BW over all possible measurement is the
fidelity F between ρ0 and ρ1. So, we have 1 ≥ F ≥ (1 − 2ε)." For density matrices `ρ_0, ρ_1`
satisfying Bob's criterion `|PE − ½| ≤ ε` for every guess (`IsConcealing ε ρ_0 ρ_1`),
`1 − 2ε ≤ F(ρ_0, ρ_1) ≤ 1`.

**Formalization Note.** `F` is the published `QAlgorithms.rootFidelity`,
`Tr √(√ρ_0 ρ_1 √ρ_0)`, not squared. -/
theorem rootFidelity_bounds_of_concealing {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ0 ρ1 : Matrix ι ι ℂ) (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) (ε : ℝ)
    (hc : IsConcealing ε ρ0 ρ1) :
    1 - 2 * ε ≤ rootFidelity ρ0 ρ1 ∧ rootFidelity ρ0 ρ1 ≤ 1 := by sorry

end MayersBC
