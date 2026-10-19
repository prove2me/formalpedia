-- Prove2me | Theorems.Thm_MazurTransfer_GlueDataPrimeOverlapCompatibility_glue_condition
-- name    : MazurTransfer.GlueDataPrimeOverlapCompatibility.glue_condition
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:20:54.958561+00:00
-- url     : https://prove2.me/theorems/5ee9baa4-1525-4b10-b713-ed562b84bba0
-- title:
--   The gluing condition for distinct charts without implementation casts
-- statement:
--   Let $D$ be a gluing datum for schemes and let $i\ne j$ be chart indices. Its transition map and chart inclusions satisfy $$t_{ij}\circ f_{ji}\circ\iota_j=f_{ij}\circ\iota_i,$$ with composition read in the formal diagram order. This is the gluing condition expressed on the specified distinct-chart overlap, and supplies the literal ordinary/reciprocal chart comparison.
-- source:
--   Original complete glue_condition statement and proof from MazurTheorem GlueDataPrimeOverlapCompatibility.lean, Apache-2.0, Vas and contributors. The original private cancellation helper is retained in an explicit fresh namespace, and original open scopes are restored at the top-level theorem. The full original closed type is kernel-compared. Named downstream consumer: the actual order-13 chart-overlap function-field comparison.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: remove implementation casts from the gluing condition of
a distinct-chart gluing datum. Named downstream consumer: the actual
order-13 overlap comparison, under the default proof checking limits.
-/
import Mathlib

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem MazurTransfer.GlueDataPrimeOverlapCompatibility.glue_condition (D : GlueData' Scheme.{u})
    [HasMulticoequalizer (GlueData.ofGlueData' D).diagram]
    (i j : D.J) (h : i ≠ j) :
    D.t i j h ≫ D.f j i h.symm ≫ (GlueData.ofGlueData' D).ι j =
      D.f i j h ≫ (GlueData.ofGlueData' D).ι i := by sorry
