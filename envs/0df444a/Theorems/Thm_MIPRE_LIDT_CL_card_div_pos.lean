-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_card_div_pos
-- name    : MIPRE.LIDT.CL.card_div_pos
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:14:04.099372+00:00
-- url     : https://prove2.me/theorems/f0a8f76e-5a9c-4248-9689-24d590a3cf91
-- title:
--   The block size q / m, positive and with m * (q/m) = q
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.CLGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded CL low individual degree test. Blueprint `def:lidt-cl`, the paper's typed low-degree game `game^ld` (`ldt.tex`, `sec:ld-game` and `fig:ld-decider`), with parameters `(q, m, d, ldc)`, `q = #F` admissible and `m ∣ q`. This is the test the paper's padded and simultaneous Pauli uses, and it is *not* the canonical-line test `MIPRE.LIDT.lidtGame` whose soundness is formalized: the two differ in which lines they sample and in how they label answers, which is the whole content of `lem:lidt-reduction-setup`.
--
--   The block size `q / m`, positive and with `m * (q/m) = q`.
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
--   theorem MIPRE.LIDT.CL.card_div_pos [NeZero m] (hm : m ∣ Fintype.card F) : 0 < Fintype.card F / m
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.card_div_pos` is declared in `MIPRE/Background/LIDT/CLGame.lean`, lines 100–104. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/CLGame.lean#L100-L104

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

theorem MIPRE.LIDT.CL.card_div_pos [NeZero m] (hm : m ∣ Fintype.card F) : 0 < Fintype.card F / m := by sorry
