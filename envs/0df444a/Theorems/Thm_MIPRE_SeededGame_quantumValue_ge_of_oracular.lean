-- Prove2me | Theorems.Thm_MIPRE_SeededGame_quantumValue_ge_of_oracular
-- name    : MIPRE.SeededGame.quantumValue_ge_of_oracular
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:00.848463+00:00
-- url     : https://prove2.me/theorems/7c165afa-ad49-483d-ba94-325a453a8ed2
-- title:
--   Soundness of oracularization, in quantum values: val* of the oracularized game above 1 - ε puts val* of the input game at least 1 - 24√ε
-- statement:
--   A statement of the module `MIPRE.Foundations.OracularTensor` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of oracularization, for bipartite strategies. Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so `val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`. `MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That is not the statement a verifier-level consumer can use:…
--
--   **Soundness of oracularization, in quantum values**: `val*` of the oracularized game above
--   `1 - ε` puts `val*` of the input game at least `1 - 24√ε`. This is the form a verifier-level
--   statement consumes, `Verifier.valStar` being a quantum value.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SeededGame
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
--   variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
--   variable (S : SeededGame V A)
--   variable {S}
--   variable (S)
--
--   theorem MIPRE.SeededGame.quantumValue_ge_of_oracular {ε : ℝ} (hε : 0 < ε)
--       (h : 1 - ε < quantumValue S.oracular.toGame) :
--       1 - 24 * √ε ≤ quantumValue S.toGame
--   ```
--
--   **Formalization Note** `MIPRE.SeededGame.quantumValue_ge_of_oracular` is declared in `MIPRE/Foundations/OracularTensor.lean`, lines 743–767. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularTensor.lean#L743-L767; blueprint lem:oracular-soundness-tensor

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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor

open MIPRE
open MIPRE.SeededGame
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
variable (S)

theorem MIPRE.SeededGame.quantumValue_ge_of_oracular {ε : ℝ} (hε : 0 < ε)
    (h : 1 - ε < quantumValue S.oracular.toGame) :
    1 - 24 * √ε ≤ quantumValue S.toGame := by sorry
