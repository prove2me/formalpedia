-- Prove2me | Theorems.Thm_Grunbaum2003_rayMachine_constant_printer
-- name    : Grunbaum2003.rayMachine_constant_printer
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:07:24.561209+00:00
-- url     : https://prove2.me/theorems/517fcf0f-b0b2-4b7f-98e3-e8ba2d5948fb
-- title:
--   A ray machine can print any finite rational tape without queries
-- statement:
--   Let $c_0,\ldots,c_{N-1}$ be any finite list of rational numbers. There is a finite ray-machine program, depending only on this list, such that in every ambient dimension and for every oracle, the program starts from the zero configuration, executes exactly $N$ steps, and halts with tape cells $0,\ldots,N-1$ equal to the prescribed rational numbers. Its tape head remains at zero and it makes no oracle queries.
--
--   This isolates output construction from geometric reconstruction: once a finite face-incidence matrix is known, its rational encoding can be written using only constant instructions.
-- source:
--   Direct consequence of Grunbaum2003.RayInstruction, RayConfiguration, rayMachineStep and rayMachineRun, the fixed exact-real query-machine definitions attached to Grünbaum (2003), §3.6, ray-oracle reconstruction. https://prove2.me/theorems/60ec78e9-77c6-458e-8d47-5b17e861648a

import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace Grunbaum2003

theorem rayMachine_constant_printer (cells : List ℚ) :
    ∃ program : List RayInstruction,
      ∀ (d : ℕ) (oracle : (Fin d → ℝ) → (Fin d → ℝ)),
        ∃ c : RayConfiguration,
          rayMachineRun program oracle cells.length
            ⟨0, 0, fun _ => 0, 0⟩ = some c ∧
          program[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = 0 ∧
          ∀ i : Fin cells.length, c.tape (i.val : ℤ) = (cells.get i : ℝ) := by sorry

end Grunbaum2003
