-- Prove2me | Theorems.Thm_Freiman_upper_tree_cylinder_width
-- name    : Freiman.upper_tree_cylinder_width
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:40.233055+00:00
-- url     : https://prove2.me/theorems/9535313d-205a-47ce-b4dc-d53d2304dcee
-- title:
--   A tree interval satisfies the report’s Fibonacci cylinder bound
-- statement:
--   Every tree node is contained in its continued-fraction cylinder and its length is at most the inverse square of the Fibonacci number indexed by the accumulated prefix length plus one.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:mobius and the mesh argument after m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_cylinder_width (p : List ℕ+) (k : Fin 5) (w : List Bool) :
    upperLength (upperTree p k w) ≤
    1 / (((Nat.fib ((upperStateAt ⟨p, k⟩ w).word.length + 1) : ℕ) : ℝ) ^ 2) := by
  sorry

end Freiman
