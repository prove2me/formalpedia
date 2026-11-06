-- Prove2me | Theorems.Thm_OAI_GaussianMoment_gaussian_moment_term_bound
-- name    : OAI.GaussianMoment.gaussian_moment_term_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:48:59.175597+00:00
-- url     : https://prove2.me/theorems/fbac12fb-61c1-4628-99ad-bbf9fd557ce8
-- title:
--   Gaussian Moment: gaussian moment term bound
-- statement:
--   The Gaussian Moment construction uses the gaussian moment term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L36-L47
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L36-L47

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.GaussianMoment

theorem OAI.GaussianMoment.gaussian_moment_term_bound (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
    q * Real.exp (-t * q) ≤
      (2 / t) * Real.exp (-(t * q / 2)) := by sorry
