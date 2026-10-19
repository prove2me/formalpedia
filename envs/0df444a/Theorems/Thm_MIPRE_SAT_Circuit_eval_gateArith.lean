-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_eval_gateArith
-- name    : MIPRE.SAT.Circuit.eval_gateArith
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:51.035019+00:00
-- url     : https://prove2.me/theorems/7b6392af-0f41-4ef2-ac62-87cd4f199f91
-- title:
--   Boolean evaluation of a gate's polynomial
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.CircuitArithmetization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bounded-degree circuit consistency polynomials. In characteristic two, `1 + w + rhs` is the indicator of Boolean gate consistency. Input-copy routing bounds the uses of external variables as well as gate variables. The output literal is included explicitly.
--
--   Boolean evaluation of a gate's polynomial.
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
--   theorem MIPRE.SAT.Circuit.eval_gateArith (C : Circuit) (k : ℕ) (g : Gate) (x w : ℕ → Bool)
--       (href : ∀ u ∈ g.refs, u < k) :
--       MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
--         (C.gateArith k g) = ofBool (g.eval
--           (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j))
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.eval_gateArith` is declared in `MIPRE/Foundations/SAT/CircuitArithmetization.lean`, lines 157–183. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/CircuitArithmetization.lean#L157-L183

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

theorem MIPRE.SAT.Circuit.eval_gateArith (C : Circuit) (k : ℕ) (g : Gate) (x w : ℕ → Bool)
    (href : ∀ u ∈ g.refs, u < k) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      (C.gateArith k g) = ofBool (g.eval
        (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)) := by sorry
