-- Prove2me | Theorems.Thm_MIPRE_LIDT_Simul_eval_pevY
-- name    : MIPRE.LIDT.Simul.eval_pevY
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:23.624393+00:00
-- url     : https://prove2.me/theorems/5e6d3d80-27f6-44d0-9069-ca303c70afce
-- title:
--   Lemma eval_pevY of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Extraction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting exactly linear combined codewords. Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of `lem:ld-soundness` for general `ldc` (`ldt.tex`, Claims 4 and 5 and the measurements `H`, `G`). The simultaneous test with `r` codewords is reduced to the single-codeword test in `K + m` variables by *combining*: a point `(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where `b ∈ F^r` is the original point answer at `y`. The single-codeword theorem then returns a measurement `R` of polynomials `g` in the `K + m` variables, consistent with the combined point answers.…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Simul
--   open Finset MIPRE MIPRE.LIDT
--   open scoped Kronecker
--   variable {F : Type*} [Field F] {K m d r : ℕ}
--
--   theorem MIPRE.LIDT.Simul.eval_pevY (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (x : Point F K)
--       (y : Point F m) : (pevY g y).eval x = g.eval (Fin.append x y)
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Simul.eval_pevY` is declared in `MIPRE/Background/LIDT/Extraction.lean`, lines 77–90. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Extraction.lean#L77-L90; blueprint lem:lidt-ldc-extraction

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
variable {F : Type*} [Field F] {K m d r : ℕ}

theorem MIPRE.LIDT.Simul.eval_pevY (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (x : Point F K)
    (y : Point F m) : (pevY g y).eval x = g.eval (Fin.append x y) := by sorry
