-- Prove2me | Theorems.Thm_MIPRE_LIDT_Simul_sum_uniform_pad
-- name    : MIPRE.LIDT.Simul.sum_uniform_pad
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:39.534423+00:00
-- url     : https://prove2.me/theorems/18748132-299b-4602-acd1-2024b9b1d3b3
-- title:
--   The uniform padded point is a uniform pair
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Extraction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting exactly linear combined codewords. Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of `lem:ld-soundness` for general `ldc` (`ldt.tex`, Claims 4 and 5 and the measurements `H`, `G`). The simultaneous test with `r` codewords is reduced to the single-codeword test in `K + m` variables by *combining*: a point `(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where `b ∈ F^r` is the original point answer at `y`. The single-codeword theorem then returns a measurement `R` of polynomials `g` in the `K + m` variables, consistent with the combined point answers.…
--
--   **The uniform padded point is a uniform pair.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Simul
--   open Finset MIPRE MIPRE.LIDT
--   open scoped Kronecker
--   open Matrix
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
--
--   theorem MIPRE.LIDT.Simul.sum_uniform_pad (f : Point F K → Point F m → ℝ) :
--       ∑ u : Point F (K + m), uniform (Point F (K + m)) u * f (xOf u) (yOf u)
--         = ∑ y : Point F m, uniform (Point F m) y *
--             ∑ x : Point F K, uniform (Point F K) x * f x y
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Simul.sum_uniform_pad` is declared in `MIPRE/Background/LIDT/Extraction.lean`, lines 474–494. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Extraction.lean#L474-L494; blueprint lem:lidt-ldc-extraction

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
open Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [DecidableEq F]

theorem MIPRE.LIDT.Simul.sum_uniform_pad (f : Point F K → Point F m → ℝ) :
    ∑ u : Point F (K + m), uniform (Point F (K + m)) u * f (xOf u) (yOf u)
      = ∑ y : Point F m, uniform (Point F m) y *
          ∑ x : Point F K, uniform (Point F K) x * f x y := by sorry
