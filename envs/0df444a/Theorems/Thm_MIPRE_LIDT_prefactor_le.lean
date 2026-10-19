-- Prove2me | Theorems.Thm_MIPRE_LIDT_prefactor_le
-- name    : MIPRE.LIDT.prefactor_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:51.026607+00:00
-- url     : https://prove2.me/theorems/ebd91286-daf6-440f-811b-38f0b3e67720
-- title:
--   The prefactor. 100000 k² m⁴ · 3md ≤ 1.92·10^11 (dm)^11 ≤ a (dm)^a
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Parameters` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 7: the parameter corollary. The reduction of `Adapter/Reduction.lean` concludes with the *canonical-line* error `lidtError m d q k (3m ε)`, with `k` free subject to `k ≥ 400 m d`. Blueprint `thm:lidt-cl-soundness` asks instead for `δ_CL(ε, q, m, d, 1) = a (dm)^a (ε^b + q^{-b} + 2^{-bmd})`, for universal `a ≥ 1` and `0 < b < 1`. `rem:lidt-cl-adapter` lists turning one into the other as a separate quantitative obligation, to be done "honestly against the explicit constants"; this file does it, and is stated separately from the reduction so that a failure here could…
--
--   **The prefactor.** `100000 k² m⁴ · 3md ≤ 1.92·10^11 (dm)^11 ≤ a (dm)^a`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--
--   theorem MIPRE.LIDT.prefactor_le (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
--       100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d)
--         ≤ clA * ((d * m : ℕ) : ℝ) ^ clA
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.prefactor_le` is declared in `MIPRE/Background/LIDT/Adapter/Parameters.lean`, lines 142–172. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Parameters.lean#L142-L172

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Parameters

open MIPRE
open MIPRE.LIDT

theorem MIPRE.LIDT.prefactor_le (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    100000 * (clK m d : ℝ) ^ 2 * (m : ℝ) ^ 4 * (3 * (m : ℝ) * d)
      ≤ clA * ((d * m : ℕ) : ℝ) ^ clA := by sorry
