-- Prove2me | Theorems.Thm_GDGen3_rootPoly_actual
-- name    : GDGen3.rootPoly_actual
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-12T06:24:11.770129+00:00
-- url     : https://prove2.me/theorems/cc43c34f-5304-4936-9105-da7510efc0e9
-- title:
--   General-N certificate lemma: rootPoly_actual
-- statement:
--   Lemma `rootPoly_actual` of the general-N certificate (manuscript sections 4-5), stated with index sequences over ℕ so that no concrete N is ever expanded.
-- source:
--   Companion supplementary proofs, Part III: the complete curve for the final gradient norm of GD. Formalized algebraic certificate layer: GD_General.lean, namespace GDGen3.

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

namespace GDGen3

lemma rootPoly_actual (r : ℝ) (N i : ℕ) (x : ℝ) :
    rootPoly r (M r N) i x = pj r (i + 1) * x * (1 + x + C r N i) - X r N i := by sorry
