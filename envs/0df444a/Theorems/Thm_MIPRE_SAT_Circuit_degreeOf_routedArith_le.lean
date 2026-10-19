-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_degreeOf_routedArith_le
-- name    : MIPRE.SAT.Circuit.degreeOf_routedArith_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:19.092999+00:00
-- url     : https://prove2.me/theorems/da567396-decc-401d-b6ed-8bb11e643a4f
-- title:
--   A degree-five bound for the characteristic-two construction, stronger than the degree-six bound required by the PCP interface
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.CircuitArithmetization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bounded-degree circuit consistency polynomials. In characteristic two, `1 + w + rhs` is the indicator of Boolean gate consistency. Input-copy routing bounds the uses of external variables as well as gate variables. The output literal is included explicitly.
--
--   A degree-five bound for the characteristic-two construction, stronger than
--   the degree-six bound required by the PCP interface.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   open MvPolynomial MIPRE.LowDegree Finset
--   variable {F : Type*} [Field F]
--
--   theorem MIPRE.SAT.Circuit.degreeOf_routedArith_le (C : Circuit) (hC : C.WellFormed) (v : ℕ ⊕ ℕ) :
--       (C.routedArith (F := F)).degreeOf v ≤ 5
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.degreeOf_routedArith_le` is declared in `MIPRE/Foundations/SAT/CircuitArithmetization.lean`, lines 131–155. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/CircuitArithmetization.lean#L131-L155; blueprint lem:pcp-circuit-arithmetization

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MvPolynomial MIPRE.LowDegree Finset
variable {F : Type*} [Field F]

theorem MIPRE.SAT.Circuit.degreeOf_routedArith_le (C : Circuit) (hC : C.WellFormed) (v : ℕ ⊕ ℕ) :
    (C.routedArith (F := F)).degreeOf v ≤ 5 := by sorry
