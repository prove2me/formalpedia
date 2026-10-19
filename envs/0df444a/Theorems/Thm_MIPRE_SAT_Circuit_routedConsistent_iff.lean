-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_routedConsistent_iff
-- name    : MIPRE.SAT.Circuit.routedConsistent_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:52.4149+00:00
-- url     : https://prove2.me/theorems/dc44e185-1a13-4b1b-9b8a-0a904d4acc1e
-- title:
--   Routing imposes exactly the original gate values on all the same variables
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.InputRouting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Routing repeated input reads through their preceding copies. `Circuit.WellFormed` bounds gate fan-out, but permits arbitrarily many gates to read the same external input. For bounded-degree consistency polynomials, the first such gate reads the external variable and each later one reads the preceding input gate's variable. This changes neither the variables nor the Boolean gate values. Each variable supplies at most one of these copy links.
--
--   Routing imposes exactly the original gate values on all the same variables.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--
--   theorem MIPRE.SAT.Circuit.routedConsistent_iff (C : Circuit) (x w : ℕ → Bool) :
--       C.RoutedConsistent x w ↔ ∀ k < C.size, w k = C.valueAt x k
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.routedConsistent_iff` is declared in `MIPRE/Foundations/SAT/InputRouting.lean`, lines 114–140. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/InputRouting.lean#L114-L140; blueprint lem:pcp-circuit-arithmetization

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit

theorem MIPRE.SAT.Circuit.routedConsistent_iff (C : Circuit) (x w : ℕ → Bool) :
    C.RoutedConsistent x w ↔ ∀ k < C.size, w k = C.valueAt x k := by sorry
