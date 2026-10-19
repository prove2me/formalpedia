-- Prove2me | Theorems.Thm_MIPRE_LIDT_LowIndDegPoly_eval_blockPoly
-- name    : MIPRE.LIDT.LowIndDegPoly.eval_blockPoly
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:51.760743+00:00
-- url     : https://prove2.me/theorems/5fb8d657-679b-46ee-bda8-911132e82907
-- title:
--   A vector supported on the range of idx evaluates through the block
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.BlockPoly` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A polynomial on a block of the variables. A coefficient vector in `n` variables read on a block of them, as a coefficient vector in the block's `n'` variables (`LowIndDegPoly.blockPoly`), and the exponent vectors that carry it (`expandIdx`). Moved from `MIPRE/Background/QLD/Complete.lean`, where the Pauli basis test's completion uses them, so that answer reduction can use them without importing that test.
--
--   **A vector supported on the range of `idx` evaluates through the block.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.LowIndDegPoly
--   open Finset
--   variable {F : Type*} [Field F] {n n' d : ℕ}
--
--   theorem MIPRE.LIDT.LowIndDegPoly.eval_blockPoly {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
--       {H : LowIndDegPoly (F := F) (m := n) (d := d)}
--       (hsupp : ∀ e, H e ≠ 0 → ∀ k, (∀ j, idx j ≠ k) → e k = 0) (u : Point F n) :
--       (H.blockPoly idx).eval (fun j => u (idx j)) = H.eval u
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.LowIndDegPoly.eval_blockPoly` is declared in `MIPRE/Background/LIDT/BlockPoly.lean`, lines 62–88. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/BlockPoly.lean#L62-L88; blueprint lem:qld-global-complete

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_BlockPoly

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.LowIndDegPoly
open Finset
variable {F : Type*} [Field F] {n n' d : ℕ}

theorem MIPRE.LIDT.LowIndDegPoly.eval_blockPoly {idx : Fin n' → Fin n} (hinj : Function.Injective idx)
    {H : LowIndDegPoly (F := F) (m := n) (d := d)}
    (hsupp : ∀ e, H e ≠ 0 → ∀ k, (∀ j, idx j ≠ k) → e k = 0) (u : Point F n) :
    (H.blockPoly idx).eval (fun j => u (idx j)) = H.eval u := by sorry
