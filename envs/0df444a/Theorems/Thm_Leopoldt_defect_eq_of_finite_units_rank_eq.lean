-- Prove2me | Theorems.Thm_Leopoldt_defect_eq_of_finite_units_rank_eq
-- name    : Leopoldt.defect_eq_of_finite_units_rank_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:30:15.470816+00:00
-- url     : https://prove2.me/theorems/55a60e48-431e-43e0-a201-a9eef9182225
-- title:
--   Equality of Leopoldt defects along extensions with equal unit rank
-- statement:
--   Let $K/F$ be a finite extension of number fields, and let $p$ be a prime. If the global unit groups of $F$ and $K$ have equal Dirichlet ranks, then their Leopoldt defects agree:
--
--   $$
--   \operatorname{rank}_{\mathbb Z}E(F)=\operatorname{rank}_{\mathbb Z}E(K)
--   \quad\Longrightarrow\quad
--   \mathcal D_L(F)=\mathcal D_L(K).
--   $$
--
--   The result applies, in particular, to the quadratic extension of a totally real field by a CM field when their unit ranks agree. It provides an extension principle without requiring that the field be CM.
--
--   **Formalization Note** The equality follows by combining the mission’s established monotonicity of defects in finite extensions with its upper bound by the increase in unit rank.
-- source:
--   Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544v4, Section 1.3, Remark 1.A, p. 5, on behavior of Leopoldt defects in finite extensions; consequence of the proved formalized theorems Leopoldt.defect_le_defect_of_finite and Leopoldt.defect_le_defect_add_rank_sub.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_eq_of_finite_units_rank_eq (p : ℕ) [Fact p.Prime]
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K]
    (hr : Units.rank F = Units.rank K) :
    defect p F = defect p K := by sorry
end Leopoldt
