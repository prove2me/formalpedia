-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_mem_unitaryGroup_three_of_star_mul_self
-- name    : KobayashiMaskawa1973.mem_unitaryGroup_three_of_star_mul_self
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:17:31.129992+00:00
-- url     : https://prove2.me/theorems/5f69a82c-4be5-40ed-a760-0973e63b04ea
-- title:
--   A 3x3 matrix with star left inverse is unitary
-- statement:
--   For any $3 \times 3$ complex matrix $U \in \mathrm{M}_3(\mathbb{C})$, if $U^\dagger U = I$, then $U$ belongs to the unitary group $\mathrm{U}(3)$:
--
--   $$U^\dagger U = I \implies U \in \mathrm{U}(3).$$
--
--   Because the underlying index set $\mathrm{Fin}\ 3$ is finite and $\mathbb{C}$ is a commutative ring, any left inverse of a square matrix is also a right inverse ($U U^\dagger = I$), which establishes membership in `Matrix.unitaryGroup (Fin 3) ℂ`.
-- source:
--   Mathlib.LinearAlgebra.UnitaryGroup

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem mem_unitaryGroup_three_of_star_mul_self (U : Matrix (Fin 3) (Fin 3) ℂ) (h : star U * U = 1) :
    U ∈ Matrix.unitaryGroup (Fin 3) ℂ := by sorry

end KobayashiMaskawa1973
