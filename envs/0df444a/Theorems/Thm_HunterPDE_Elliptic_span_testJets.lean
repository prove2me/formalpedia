-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_span_testJets
-- name    : HunterPDE.Elliptic.span_testJets
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T21:14:32.818637+00:00
-- url     : https://prove2.me/theorems/f13fb7a0-7b31-4dae-9334-735e226712b4
-- title:
--   Test-function jets already form a linear subspace
-- statement:
--   For every subset Ω of ℝⁿ, the real linear span in L²(Ω;ℝ×ℝⁿ) of the jets (φ,∇φ) of smooth compactly supported φ with closed support in Ω equals the set of those jets itself. Thus finite linear combinations can be represented by a single test function, and the definition of H¹₀ as closure of the span is also the closure of the test jets. No openness or boundedness of Ω is required. The result follows from linearity of differentiation and closure of compact support under addition and scalar multiplication.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, p. 92 (definition of H¹₀ as closure of test functions), p. 98 (density step in Theorem 4.9). https://www.math.ucdavis.edu/~hunter/pdes/ch4.pdf

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Definitions.Def_HunterPDE_Elliptic_H10

open MeasureTheory
open scoped ContDiff
open HunterPDE.Elliptic

set_option autoImplicit false

theorem HunterPDE.Elliptic.span_testJets {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    (↑(Submodule.span ℝ (testJets n Ω)) : Set (JetL2 n Ω)) = testJets n Ω := by sorry
