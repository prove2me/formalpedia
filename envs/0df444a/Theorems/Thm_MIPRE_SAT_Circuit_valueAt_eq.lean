-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_valueAt_eq
-- name    : MIPRE.SAT.Circuit.valueAt_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:25:54.643532+00:00
-- url     : https://prove2.me/theorems/34d6779e-3e58-4114-abce-4face351c76c
-- title:
--   Lemma valueAt_eq of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Circuit` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Boolean circuits as data. The circuits of the succinct Cook–Levin theorem (`planning/succinct-cook-levin.md`, S0; `answer_reduction.tex` `sec:ar-tms`): a circuit is a list of gates in topological order, each gate reading input bits or the values of earlier gates, the last gate being the output. Fan-in is at most two by the shape of the gates; fan-out at most two and a terminal output gate are the well-formedness conditions (`Circuit.WellFormed`) that the arithmetization of the Tseitin formula needs for its individual-degree bound (`prop:tseitin-arith-degree`). The gate count is the paper's…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   open MIPRE.Cost
--
--   theorem MIPRE.SAT.Circuit.valueAt_eq (C : Circuit) (x : ℕ → Bool) (g : ℕ) :
--       C.valueAt x g = (C.gates.getD g (.const false)).eval x (List.ofFn fun k : Fin g => C.valueAt x k)
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.valueAt_eq` is declared in `MIPRE/Foundations/SAT/Circuit.lean`, lines 115–117. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Circuit.lean#L115-L117

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MIPRE.Cost

theorem MIPRE.SAT.Circuit.valueAt_eq (C : Circuit) (x : ℕ → Bool) (g : ℕ) :
    C.valueAt x g = (C.gates.getD g (.const false)).eval x (List.ofFn fun k : Fin g => C.valueAt x k) := by sorry
