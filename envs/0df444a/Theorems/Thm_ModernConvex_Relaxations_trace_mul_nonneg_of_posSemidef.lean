-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_trace_mul_nonneg_of_posSemidef
-- name    : ModernConvex.Relaxations.trace_mul_nonneg_of_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:28.615739+00:00
-- url     : https://prove2.me/theorems/da829fe8-ce17-418b-b8dd-b0ab17e6e846
-- title:
--   Trace pairing of semidefinite matrices is nonnegative
-- statement:
--   For real symmetric matrices $Z\succeq 0$ and $X\succeq0$ of the same order, the trace of the product is nonnegative: $\operatorname{tr}(ZX)\ge 0$.
--
--   Write $Z=B^{\mathsf T}B$ (a positive semidefinite matrix is a Gram matrix). Then $\operatorname{tr}(ZX)=\operatorname{tr}(B^{\mathsf T}BX)=\operatorname{tr}(BXB^{\mathsf T})$ by cyclicity of the trace, and $BXB^{\mathsf T}$ is again positive semidefinite, hence has nonnegative trace. This is the elementary fact behind weak duality for semidefinite programs: the pairing of a primal feasible and a dual slack matrix measures the duality gap.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, §4.3.3-4.3.4, pp. 170-174; the elementary inequality behind weak duality for the MAXCUT SDP (4.3.15).

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The trace pairing of positive semidefinite matrices is nonnegative.** If `Z ⪰ 0` and
`X ⪰ 0` then `0 ≤ (Z * X).trace`. -/
theorem trace_mul_nonneg_of_posSemidef {n : ℕ} {Z X : Matrix (Fin n) (Fin n) ℝ}
    (hZ : Z.PosSemidef) (hX : X.PosSemidef) : 0 ≤ (Z * X).trace := by sorry

end ModernConvex.Relaxations
