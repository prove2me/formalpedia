-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_mem_frameBody
-- name    : MIPRE.TM.Interp.mem_frameBody
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:57.503503+00:00
-- url     : https://prove2.me/theorems/5a7d0106-e4ff-4650-b9d8-c33b96b37879
-- title:
--   No $ in the body of a frame
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Repr` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The tape representation of configurations. Values as their preorder bits (`S`), the control (`ctrlRepr`), the environment (`envRepr`, innermost value at the right end, `#`-separated), the frames (`frameRepr`) and the stack (`kontRepr`), as lists of symbols; and their lengths in terms of the sizes.
--
--   No `$` in the body of a frame.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.Interp
--   open MIPRE.Cost MIPRE.Cost.Machine
--
--   theorem MIPRE.TM.Interp.mem_frameBody (f : Frame) : ∀ s ∈ frameBody f, s ≠ .fr
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.mem_frameBody` is declared in `MIPRE/TM/Interp/Repr.lean`, lines 98–137. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Repr.lean#L98-L137

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Repr

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open MIPRE.Cost MIPRE.Cost.Machine

theorem MIPRE.TM.Interp.mem_frameBody (f : Frame) : ∀ s ∈ frameBody f, s ≠ .fr := by sorry
