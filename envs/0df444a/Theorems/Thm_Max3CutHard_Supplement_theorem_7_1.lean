-- Prove2me | Theorems.Thm_Max3CutHard_Supplement_theorem_7_1
-- name    : Max3CutHard.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:50:41.117425+00:00
-- url     : https://prove2.me/theorems/b69d8350-863e-4f2e-9d63-a5cbfb05a685
-- title:
--   Theorem 7.1 — barrier: $\max_xS_{y^\circ}(x)\ge\frac{27}{29}\sum_tC_t$ for every Max-3-Cut family; $\rho\ge27/29$, attained by $(2E,N,N)$
-- statement:
--   **Theorem 7.1 (computer-assisted).** For every family $(I_0,I_1,I_2)$ of Max-3-Cut gadgets with non-negative edge weights (with any number of auxiliary vertices, possibly using the global vertices),
--
--   $$\max_{x\in\mathbb Z_3^3}S_{y^\circ}(x)\ \ge\ \frac{27}{29}\sum_{t\in\mathbb Z_3}C_t,$$
--
--   where $y^\circ=(0,1,2)$ is the canonical colouring of the globals. Hence Theorem 4.1 cannot give a ratio below $27/29$ for Max-3-Cut, and the family of Section 3 is optimal for it:
--
--   1. every such family with $\sum_tC_t>0$ has $\rho\ge27/29$;
--   2. the family $(2E,N,N)$ of Section 3 has $\rho=27/29$.
--
--   The theorem shows that the bound $27/29$ of Theorem 1.1 is the limit of the soundness criterion for Max-3-Cut, for gadgets of any size; going further requires changing the source problem, the form of the reduction, or the analysis.
--
--   Differences from the source:
--   - reading: Hence Theorem 4.1 cannot give a ratio below 27/29 for Max-3-Cut, and the family of Section 3 is optimal for it → ρ(F) ≥ 27/29 for every non-negatively weighted family F with Σ_t C_t > 0, and ρ(family0) = 27/29; reason: ρ is the ratio Theorem 4.1 gives; the hypothesis Σ_t C_t > 0 is where ρ is defined
--   - encoding: colours Z3, y◦ = (0, 1, 2) → Fin 3, id : Fin 3 → Fin 3; reason: Lean convention; same instances
--   - generalization: gadgets are weighted graphs with edges {u, v} (Section 2) → every published Gadget 3 with non-negative weights, whose edge list may also contain loops; reason: a loop is never cut and enters neither V_t nor C_t, so deleting the loops gives a gadget of the paper with the same S_{y◦}, C_t and ρ; the Lean statement specializes to the paper's on loopless gadgets
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 7.1, p.12

import Mathlib
import Definitions.Def_Max3CutHard_IsNonneg
import Definitions.Def_Max3CutHard_Family
import Definitions.Def_Max3CutHard_Ct
import Definitions.Def_Max3CutHard_family0
import Definitions.Def_Max3CutHard_Supplement_Sval
import Definitions.Def_Max3CutHard_Supplement_rho

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **Theorem 7.1 (computer-assisted).** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 7.1, p.12: "For every family
`(I0, I1, I2)` of Max-3-Cut gadgets (with any number of auxiliary vertices, possibly using the
global vertices), `max_{x∈Z3^3} S_{y◦}(x) ≥ 27/29 Σ_t C_t`. Hence Theorem 4.1 cannot give a ratio
below `27/29` for Max-3-Cut, and the family of Section 3 is optimal for it."

**Formalization Note.** `k = 3`, colours `Z3 = Fin 3`, `y◦ = id`; gadgets are the published
`Gadget 3` with non-negative weights (`IsNonneg`) and edges allowed at the globals. The first
clause is the displayed inequality (maximum over `x` only, at `y = y◦`). The "Hence" sentence is
the second and third clauses: `ρ ≥ 27/29` for every family with `Σ_t C_t > 0` (where `ρ` is
defined), and `ρ = 27/29` for the published family `family0 = (2E, N, N)` of Section 3. -/
theorem theorem_7_1 :
    (∀ F : Family 3, (∀ t : ZMod 3, IsNonneg (F t).edges) →
      (27 / 29 : ℝ) * ∑ t : ZMod 3, Ct le_rfl F t ≤
        Finset.univ.sup' Finset.univ_nonempty (fun x : Fin 3 → Fin 3 => Sval F x id)) ∧
    (∀ F : Family 3, (∀ t : ZMod 3, IsNonneg (F t).edges) →
      0 < ∑ t : ZMod 3, Ct le_rfl F t → (27 / 29 : ℝ) ≤ rho le_rfl F) ∧
    rho le_rfl family0 = 27 / 29 := by sorry

end Max3CutHard.Supplement
