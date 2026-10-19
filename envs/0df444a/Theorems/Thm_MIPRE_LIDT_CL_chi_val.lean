-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_chi_val
-- name    : MIPRE.LIDT.CL.chi_val
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:14:12.334174+00:00
-- url     : https://prove2.me/theorems/b6f0d560-e1ee-4735-af81-c6f3767efc2f
-- title:
--   Lemma chi_val of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.CLGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded CL low individual degree test. Blueprint `def:lidt-cl`, the paper's typed low-degree game `game^ld` (`ldt.tex`, `sec:ld-game` and `fig:ld-decider`), with parameters `(q, m, d, ldc)`, `q = #F` admissible and `m ∣ q`. This is the test the paper's padded and simultaneous Pauli uses, and it is *not* the canonical-line test `MIPRE.LIDT.lidtGame` whose soundness is formalized: the two differ in which lines they sample and in how they label answers, which is the whole content of `lem:lidt-reduction-setup`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.CL
--   open Finset MIPRE.LIDT
--   variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d ldc : ℕ)
--   variable {F m}
--
--   theorem MIPRE.LIDT.CL.chi_val [NeZero m] (hm : m ∣ Fintype.card F) (s : F) :
--       (chi hm s : ℕ) = (Fintype.equivFin F s).val / (Fintype.card F / m)
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.chi_val` is declared in `MIPRE/Background/LIDT/CLGame.lean`, lines 106–108. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/CLGame.lean#L106-L108

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open Finset MIPRE.LIDT
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d ldc : ℕ)
variable {F m}
omit [DecidableEq F]

theorem MIPRE.LIDT.CL.chi_val [NeZero m] (hm : m ∣ Fintype.card F) (s : F) :
    (chi hm s : ℕ) = (Fintype.equivFin F s).val / (Fintype.card F / m) := by sorry
