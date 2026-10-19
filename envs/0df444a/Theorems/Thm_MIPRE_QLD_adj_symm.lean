-- Prove2me | Theorems.Thm_MIPRE_QLD_adj_symm
-- name    : MIPRE.QLD.adj_symm
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:06:17.500768+00:00
-- url     : https://prove2.me/theorems/1166c785-5e8f-4bcd-af7e-3589ce0d4a07
-- title:
--   Lemma adj_symm of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.QLD.Game` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Pauli basis test. Blueprint `def:qld-game`, the paper's game `game^pauli_{(q,m,d)}` (`ldt.tex`, `sec:qld-game` for the question distribution and `fig:decider_pauli` for the decision procedure). This is the game `thm:qld` is about and `lem:qld-win` unpacks. The test certifies that the players share `|EPR_q⟩^{⊗ M}`, `M = 2^m`. A player asked `(Pauli, W)` measures `{τ^W_h}_{h ∈ F_q^M}` and reports `h`; every other question probes limited information about `h` through its low-degree encoding `g_h : F_q^m → F_q` (`MIPRE.LowDegree.ldEnc`), and the subtests check that those probes are consistent…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open Finset MIPRE.LIDT MIPRE.LCS.MagicSquare
--   open MvPolynomial (eval)
--
--   theorem MIPRE.QLD.adj_symm (t u : Ty) : adj t u = adj u t
--   ```
--
--   **Formalization Note** `MIPRE.QLD.adj_symm` is declared in `MIPRE/Background/QLD/Game.lean`, lines 133–133. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Game.lean#L133-L133; blueprint def:qld-game

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
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
import Definitions.Def_MIPRE_Background_QLD_Game

open MIPRE
open MIPRE.QLD
open Finset MIPRE.LIDT MIPRE.LCS.MagicSquare
open MvPolynomial (eval)

theorem MIPRE.QLD.adj_symm (t u : Ty) : adj t u = adj u t := by sorry
