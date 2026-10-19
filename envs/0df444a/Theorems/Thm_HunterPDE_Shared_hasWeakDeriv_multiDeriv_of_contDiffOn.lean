-- Prove2me | Theorems.Thm_HunterPDE_Shared_hasWeakDeriv_multiDeriv_of_contDiffOn
-- name    : HunterPDE.Shared.hasWeakDeriv_multiDeriv_of_contDiffOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T16:36:27.642169+00:00
-- url     : https://prove2.me/theorems/74cd4318-37b5-45aa-b5de-389b1900fdf1
-- title:
--   Classical derivatives of every order are weak derivatives on open sets
-- statement:
--   Let Ω be any open subset of Euclidean space and let f be smooth on Ω. For every multi-index α, the classical derivative ∂^α f is a weak derivative of f on Ω. Both functions are locally integrable there, and the order-|α| integration by parts identity holds against all smooth compactly supported tests in Ω. No regularity of the boundary, global smoothness, compact support of f, or assumptions outside Ω are required.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definitions 3.1–3.2 and discussion printed pp.47–48, Definition 3.23 printed p.58, smooth compact closed-half-space class in Theorem 3.42 printed p.72. All-order open-set integration by parts formulation of the identification of weak and classical derivatives.

import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Theorems.Thm_HunterPDE_Shared_iteratedPartial_eq_of_perm
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Tactic.Ring

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.hasWeakDeriv_multiDeriv_of_contDiffOn {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ ∞ f Ω) (α : Fin n → ℕ) :
    HasWeakDeriv Ω α f (multiDeriv f α) := by sorry
