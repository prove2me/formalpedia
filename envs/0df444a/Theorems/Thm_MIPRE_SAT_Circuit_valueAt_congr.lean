-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_valueAt_congr
-- name    : MIPRE.SAT.Circuit.valueAt_congr
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:09.325655+00:00
-- url     : https://prove2.me/theorems/59a04344-ba88-489f-a429-ebbb9bcf22c6
-- title:
--   The gate values depend only on the inputs the circuit reads
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Tseitin` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The circuit-to-3SAT reduction. `Circuit.tseitin C inp gv` is the 3SAT formula of a circuit `C` on variables `inp i` for its inputs and `gv g` for its gates (`lem:circuit-to-sat-reduction`, `lem:tseitin` with the output-wire conjunct of the F7.2 erratum): for every gate the clauses saying that its variable is the gate's function of its arguments' variables, and the unit clause on the output gate. `tseitin_sat_iff`: for a circuit reading only earlier gates, `C(x) = 1` iff some assignment agreeing with `x` on the inputs satisfies the formula; `tseitin_values`: a satisfying assignment carries the…
--
--   The gate values depend only on the inputs the circuit reads.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   variable {V : Type*}
--
--   theorem MIPRE.SAT.Circuit.valueAt_congr (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
--       (hx : ∀ i < C.inputs, x i = x' i) : ∀ g, C.valueAt x g = C.valueAt x' g
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.valueAt_congr` is declared in `MIPRE/Foundations/SAT/Tseitin.lean`, lines 112–135. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Tseitin.lean#L112-L135

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

theorem MIPRE.SAT.Circuit.valueAt_congr (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
    (hx : ∀ i < C.inputs, x i = x' i) : ∀ g, C.valueAt x g = C.valueAt x' g := by sorry
