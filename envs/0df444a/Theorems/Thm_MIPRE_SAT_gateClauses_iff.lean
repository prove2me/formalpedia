-- Prove2me | Theorems.Thm_MIPRE_SAT_gateClauses_iff
-- name    : MIPRE.SAT.gateClauses_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:06.090708+00:00
-- url     : https://prove2.me/theorems/b1b13fc2-3ed0-438a-b791-a06cfef06e12
-- title:
--   The clauses of a gate hold iff its variable carries the gate's value, when the argument variables carry the argument values
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Tseitin` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The circuit-to-3SAT reduction. `Circuit.tseitin C inp gv` is the 3SAT formula of a circuit `C` on variables `inp i` for its inputs and `gv g` for its gates (`lem:circuit-to-sat-reduction`, `lem:tseitin` with the output-wire conjunct of the F7.2 erratum): for every gate the clauses saying that its variable is the gate's function of its arguments' variables, and the unit clause on the output gate. `tseitin_sat_iff`: for a circuit reading only earlier gates, `C(x) = 1` iff some assignment agreeing with `x` on the inputs satisfies the formula; `tseitin_values`: a satisfying assignment carries the…
--
--   The clauses of a gate hold iff its variable carries the gate's value, when the argument
--   variables carry the argument values.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   variable {V : Type*}
--
--   theorem MIPRE.SAT.gateClauses_iff (inp gv : ℕ → V) (y : V) (g : Gate) (w : V → Bool) (vals : List Bool)
--       (hv : ∀ u ∈ g.refs, vals.getD u false = w (gv u)) :
--       (∀ c ∈ gateClauses inp gv y g, c.eval w = true) ↔ w y = g.eval (fun i => w (inp i)) vals
--   ```
--
--   **Formalization Note** `MIPRE.SAT.gateClauses_iff` is declared in `MIPRE/Foundations/SAT/Tseitin.lean`, lines 43–72. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Tseitin.lean#L43-L72

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
variable {V : Type*}

theorem MIPRE.SAT.gateClauses_iff (inp gv : ℕ → V) (y : V) (g : Gate) (w : V → Bool) (vals : List Bool)
    (hv : ∀ u ∈ g.refs, vals.getD u false = w (gv u)) :
    (∀ c ∈ gateClauses inp gv y g, c.eval w = true) ↔ w y = g.eval (fun i => w (inp i)) vals := by sorry
