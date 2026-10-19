-- Prove2me | Theorems.Thm_MIPRE_QLD_MS_relation_core
-- name    : MIPRE.QLD.MS.relation_core
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:01:54.557856+00:00
-- url     : https://prove2.me/theorems/fa5860b6-22cd-4335-82b7-2f132175ffcc
-- title:
--   A within-constraint relation costs 3 γ. The two Bob letters are transported to the constraint's two Alice reflections, which costs 2 γ; their product *is* the third…
-- statement:
--   A statement of the module `MIPRE.Background.QLD.Anticomm` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Direct Magic Square anticommutation. Blueprint `lem:ms-direct-anticomm`: a strategy failing the Magic Square game with probability `ε` has `‖{B₁, B₅}|ψ⟩‖² ≤ 186624 ε` for the *original* `±1`-observables of the two players --- no isometry, no projectivity, no extracted EPR pairs. This is the only thing the Pauli basis test consumes from the Magic Square, and it is much weaker than the full rigidity theorem `thm:ms-rigidity`, which this repository does not prove.
--
--   **A within-constraint relation costs `3 γ`.** The two Bob letters are transported to the
--   constraint's two Alice reflections, which costs `2 γ`; their product *is* the third reflection
--   times the constraint's sign, with no error; and that reflection is returned to Bob for a
--   further `γ`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open MIPRE.QLD.MS
--   open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
--   open scoped ComplexOrder MatrixOrder
--   variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {MA : layout.Question → POVM layout.Answer dA}
--   variable {MB : layout.Question → POVM layout.Answer dB}
--   variable {MA : layout.Question → POVM layout.Answer dA}
--   variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}
--
--   theorem MIPRE.QLD.MS.relation_core
--       (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
--       (c : Fin layout.r) (i j : Fin 3)
--       (hij : refl D c j * refl D c i = sgn (game.b c) • refl D c 2) :
--       dd ψ (bobs MB (cell c i) * bobs MB (cell c j)) (sgn (game.b c) • bobs MB (cell c 2))
--         ≤ 3 * γ
--   ```
--
--   **Formalization Note** `MIPRE.QLD.MS.relation_core` is declared in `MIPRE/Background/QLD/Anticomm.lean`, lines 410–435. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Anticomm.lean#L410-L435

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Anticomm

open MIPRE
open MIPRE.QLD
open MIPRE.QLD.MS
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}

theorem MIPRE.QLD.MS.relation_core
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) (i j : Fin 3)
    (hij : refl D c j * refl D c i = sgn (game.b c) • refl D c 2) :
    dd ψ (bobs MB (cell c i) * bobs MB (cell c j)) (sgn (game.b c) • bobs MB (cell c 2))
      ≤ 3 * γ := by sorry
