-- Prove2me | Theorems.Thm_GDGen3_ell_root_nonneg
-- name    : GDGen3.ell_root_nonneg
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:41:28.686261+00:00
-- url     : https://prove2.me/theorems/20dc02bf-f81d-4444-bbea-0f3c06ee8f1e
-- title:
--   General-N certificate lemma: ell_root_nonneg
-- statement:
--   All off-diagonal flow multipliers are nonnegative, for arbitrary N, under the oscillatory-branch parameter condition.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma ell_root_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i j : ℕ)
    (hiN : i ≤ N) (hjN : j ≤ N) (hij : i ≠ j)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    0 ≤ ell r (rootXi r N) N i j := by sorry
