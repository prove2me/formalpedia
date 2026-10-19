-- Prove2me | Theorems.Thm_MIPRE_LIDT_lidtError_le_deltaCL
-- name    : MIPRE.LIDT.lidtError_le_deltaCL
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:14:02.557742+00:00
-- url     : https://prove2.me/theorems/7b9853cf-9ad1-41a6-93ae-c3d6693b4f0c
-- title:
--   The parameter corollary. At k = clK m d the canonical-line error on the adapter's inflated failure 3 m ε is below the blueprint's δ_CL at ldc = 1, with the explicit…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Parameters` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 7: the parameter corollary. The reduction of `Adapter/Reduction.lean` concludes with the *canonical-line* error `lidtError m d q k (3m ε)`, with `k` free subject to `k ≥ 400 m d`. Blueprint `thm:lidt-cl-soundness` asks instead for `δ_CL(ε, q, m, d, 1) = a (dm)^a (ε^b + q^{-b} + 2^{-bmd})`, for universal `a ≥ 1` and `0 < b < 1`. `rem:lidt-cl-adapter` lists turning one into the other as a separate quantitative obligation, to be done "honestly against the explicit constants"; this file does it, and is stated separately from the reduction so that a failure here could…
--
--   **The parameter corollary.** At `k = clK m d` the canonical-line error on the adapter's
--   inflated failure `3 m ε` is below the blueprint's `δ_CL` at `ldc = 1`, with the explicit
--   constants `a = 2·10^11` and `b = 1/40000`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--
--   theorem MIPRE.LIDT.lidtError_le_deltaCL (m d q : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
--       lidtError m d q (clK m d) (3 * m * ε) ≤ deltaCL q m d ε
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.lidtError_le_deltaCL` is declared in `MIPRE/Background/LIDT/Adapter/Parameters.lean`, lines 176–222. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Parameters.lean#L176-L222; blueprint lem:lidt-cl-adapter-params

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

theorem MIPRE.LIDT.lidtError_le_deltaCL (m d q : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    lidtError m d q (clK m d) (3 * m * ε) ≤ deltaCL q m d ε := by sorry
