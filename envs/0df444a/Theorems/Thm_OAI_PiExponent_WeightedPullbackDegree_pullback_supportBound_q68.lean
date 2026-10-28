-- Prove2me | Theorems.Thm_OAI_PiExponent_WeightedPullbackDegree_pullback_supportBound_q68
-- name    : OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:59:04.424674+00:00
-- url     : https://prove2.me/theorems/39523416-8dce-4bfe-970d-7abac524598f
-- title:
--   OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound` of [lean/OAI/NumberTheory/PiExponent/Approximation/WeightedPullbackDegree.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightedPullbackDegree.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.WeightedPullbackDegree`, with `open AlgebraicGeometry CategoryTheory`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective`, `open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree`, `open PiExponent.AffineJetPolynomial PiExponent.AffineJetCoefficientFrame`, `open PiExponent.AffineJetCoefficientInterface`):
--
--   ```lean
--   theorem pullback_supportBound_q68 (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
--       (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
--       (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
--       (e : Frame (affineChartMap (R := K) a z hz coordinate hcoordinate)
--         (lineBundle (R := K) a))
--       (s : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n)
--       (p : MvPolynomial.homogeneousSubmodule σ K n)
--       (hp : dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) (σ := σ) n z
--         (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s)) :
--       SupportBound ρ ((n : ℝ) * B)
--         (AffineJetCoefficientInterface.coefficient (affineChartMap (R := K) a z hz coordinate hcoordinate)
--           (lineBundle (R := K) a) n e
--           (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ))
--             (projectiveMonomialMap (R := K) a) n s))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.ProjectiveO1.projectiveSpace`, `OAI.PiExponent.WeightedCompactification.affineChartMap`, `OAI.PiExponent.WeightedCompactification.imageGrade`, `OAI.PiExponent.WeightedCompactification.imageGradedAlgebra`, `OAI.PiExponent.WeightedCompactification.monomialImage`, `OAI.PiExponent.WeightedCompactification.projectiveMonomialMap`, `OAI.PiExponentSeshadri.Projective.ChartVariables` and `OAI.PiExponentSeshadri.Projective.dehomogenize` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.WeightedSliceDegree.SupportBound` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponent.ProjectiveO1.lineBundle` and `OAI.PiExponent.WeightedCompactification.lineBundle` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponent.WeightedCompactification.affineChartMap_isOpenImmersion` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponent.ProjectiveO1.globalSectionChartPolynomial` (definitions bundle `OAIQ068A033` of this split); `OAI.PiExponent.AffineJetCoefficientInterface.Frame`, `OAI.PiExponent.AffineJetCoefficientInterface.Sections`, `OAI.PiExponent.AffineJetCoefficientInterface.coefficient` and `OAI.PiExponent.ProjectiveSectionInterface.sectionHom` (definitions bundle `OAIQ068A044` of this split); `OAI.PiExponent.ProjectiveSectionInterface.pullback` (definitions bundle `OAIQ068A046` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightedPullbackDegree.lean (declaration OAI.PiExponent.WeightedPullbackDegree.pullback_supportBound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A046

section

attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.WeightedPullbackDegree
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetPolynomial PiExponent.AffineJetCoefficientFrame
open PiExponent.AffineJetCoefficientInterface
variable {K ι σ : Type} [Field K]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  WeightedCompactification.affineChartMap
  AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  ProjectiveO1.lineBundle ProjectiveO1.coordinateSection ProjectiveO1.scalars
  ProjectiveO1.coordinateCocycle PiExponentSeshadri.Projective.sectionsMorphism
  PiExponentSeshadri.Projective.CoordinateAtlas.morphism PiExponentSeshadri.Projective.atlasOfFramedSections
  ProjectiveO1.globalSectionChartPolynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv

theorem pullback_supportBound_q68 (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
    (e : Frame (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (lineBundle (R := K) a))
    (s : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n)
    (p : MvPolynomial.homogeneousSubmodule σ K n)
    (hp : dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) (σ := σ) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s)) :
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient (affineChartMap (R := K) a z hz coordinate hcoordinate)
        (lineBundle (R := K) a) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ))
          (projectiveMonomialMap (R := K) a) n s)) := by
  sorry

end PiExponent.WeightedPullbackDegree
end

end OAI
end
