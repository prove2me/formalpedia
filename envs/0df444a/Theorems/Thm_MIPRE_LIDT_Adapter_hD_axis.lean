-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_hD_axis
-- name    : MIPRE.LIDT.Adapter.hD_axis
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:22.326627+00:00
-- url     : https://prove2.me/theorems/6d53a569-c813-4091-bb53-a4b2ac1a7277
-- title:
--   The axis-parallel case: the source checks the point is on the seeded line and the answer evaluates correctly there, and after reversal that is the same equation the target checks
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Strategy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 4: the question and answer maps. The reduction plays a strategy for the seeded CL test as a strategy for the canonical-line test, through `MIPRE.TensorProductStrategy.adapt`. That needs two maps, and this file defines them and the bookkeeping that identifies them. `qmap hm σ` sends a question of the canonical-line test to the seeded question it is played through: * a point `u` to the point `ρ u`, reversal exchanging the two diagonal conventions; * an axis-parallel line to `(ρ ℓ.1, s)` — no `rep` is needed, the two tests' base points agree exactly there…
--
--   The axis-parallel case: the source checks the point is on the seeded line and the answer
--   evaluates correctly there, and after reversal that is the same equation the target checks.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Adapter
--   open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
--   variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}
--
--   theorem MIPRE.LIDT.Adapter.hD_axis (u : Point F m) (i : Fin m) (a b : CL.Answer F m d 1)
--       (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.axisLine (Line.through u (Pi.single i 1))))
--         (qmap hm σ c (.point u)) a b = true) :
--       (lidtGame F m d).D (.axisLine (Line.through u (Pi.single i 1))) (.point u)
--         (amap c (.axisLine (Line.through u (Pi.single i 1))) a) (amap c (.point u) b) = true
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.hD_axis` is declared in `MIPRE/Background/LIDT/Adapter/Strategy.lean`, lines 253–311. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Strategy.lean#L253-L311

import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (σ : Fin m → Fin (Fintype.card F / m)) {c : F}

theorem MIPRE.LIDT.Adapter.hD_axis (u : Point F m) (i : Fin m) (a b : CL.Answer F m d 1)
    (hacc : (clGame (d := d) (ldc := 1) hm).D (qmap hm σ c (.axisLine (Line.through u (Pi.single i 1))))
      (qmap hm σ c (.point u)) a b = true) :
    (lidtGame F m d).D (.axisLine (Line.through u (Pi.single i 1))) (.point u)
      (amap c (.axisLine (Line.through u (Pi.single i 1))) a) (amap c (.point u) b) = true := by sorry
