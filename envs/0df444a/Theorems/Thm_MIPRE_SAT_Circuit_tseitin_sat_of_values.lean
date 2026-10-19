-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_tseitin_sat_of_values
-- name    : MIPRE.SAT.Circuit.tseitin_sat_of_values
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:03.439625+00:00
-- url     : https://prove2.me/theorems/49a55fcb-a298-4261-ba24-bb1a7eb86826
-- title:
--   Completeness, for a given assignment: one that carries the gate values on the gate variables satisfies the formula when the circuit accepts the bits it reads on the inputs
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Tseitin` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The circuit-to-3SAT reduction. `Circuit.tseitin C inp gv` is the 3SAT formula of a circuit `C` on variables `inp i` for its inputs and `gv g` for its gates (`lem:circuit-to-sat-reduction`, `lem:tseitin` with the output-wire conjunct of the F7.2 erratum): for every gate the clauses saying that its variable is the gate's function of its arguments' variables, and the unit clause on the output gate. `tseitin_sat_iff`: for a circuit reading only earlier gates, `C(x) = 1` iff some assignment agreeing with `x` on the inputs satisfies the formula; `tseitin_values`: a satisfying assignment carries the…
--
--   Completeness, for a given assignment: one that carries the gate values on the gate
--   variables satisfies the formula when the circuit accepts the bits it reads on the inputs.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   variable {V : Type*}
--
--   theorem MIPRE.SAT.Circuit.tseitin_sat_of_values (C : Circuit) (hC : C.RefsLt) (inp gv : ℕ → V) (w : V → Bool)
--       (hwg : ∀ g < C.gates.length, w (gv g) = C.valueAt (fun i => w (inp i)) g)
--       (hx : C.eval (fun i => w (inp i)) = true) : (C.tseitin inp gv).Sat w
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.tseitin_sat_of_values` is declared in `MIPRE/Foundations/SAT/Tseitin.lean`, lines 157–179. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Tseitin.lean#L157-L179

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

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
variable {V : Type*}

theorem MIPRE.SAT.Circuit.tseitin_sat_of_values (C : Circuit) (hC : C.RefsLt) (inp gv : ℕ → V) (w : V → Bool)
    (hwg : ∀ g < C.gates.length, w (gv g) = C.valueAt (fun i => w (inp i)) g)
    (hx : C.eval (fun i => w (inp i)) = true) : (C.tseitin inp gv).Sat w := by sorry
