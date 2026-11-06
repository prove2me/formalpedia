-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeTheta_regularizedLatticeL_differentiableAt
-- name    : OAI.SevenEighths.HeckeTheta.regularizedLatticeL_differentiableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:58.283249+00:00
-- url     : https://prove2.me/theorems/1415690c-37ce-447e-8240-f0642f967686
-- title:
--   Hecke Theta: regularized Lattice L differentiable At
-- statement:
--   The Hecke Theta construction uses the regularized Lattice L differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Theta.lean#L206-L212
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Theta.lean#L206-L212

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta

theorem OAI.SevenEighths.HeckeTheta.regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by sorry
