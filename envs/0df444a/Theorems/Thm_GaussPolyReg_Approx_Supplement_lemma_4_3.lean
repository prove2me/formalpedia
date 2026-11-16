-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_Supplement_lemma_4_3
-- name    : GaussPolyReg.Approx.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:28:19.775434+00:00
-- url     : https://prove2.me/theorems/fc7e8910-629d-405d-97af-fec295e50126
-- title:
--   Lemma 4.3 — equality forces a grade-one halfspace indicator
-- statement:
--   Let $a,s\in(0,1)$ and let $f\in L^2(Z)$ on the countable graded Gaussian space satisfy $0\le f\le1$ almost everywhere and $\mathbb Ef=a$. If
--
--   $$\operatorname{Stab}_s(f)=\operatorname{Stab}_s(H_a),\qquad H_a=(-\infty,\Phi^{-1}(a)),$$
--
--   then there are real coefficients $(c_i)_{i\in\mathbb N}$ and $t\in\mathbb R$ such that
--
--   $$\sum_i c_i^2=1,\qquad f=\mathbf1_{\{\sum_i c_iZ_{1,i}\ge t\}}\quad\text{a.e.}$$
--
--   The normal may have infinitely many nonzero entries. The Gaussian linear series is interpreted in $L^2$, so the halfspace uses only grade-one variables and changes by a null set under any representative choice. This is the complete equality characterization used by Theorem 4.1; Booleanity is a conclusion, not a hypothesis.
--
--   Differences from the source:
--   - encoding: closed Hermite chaos on countably many independent Gaussian variables of every positive grade → the published L² closed spans on I = ℕ+ × ℕ with grade (r,i) = r; reason: a fixed reindexing of exactly the source space, with a.e. classes and degree zero retained
--   - encoding: OU noise stability with correlation s on ordinary coordinates and s^r on grade-r coordinates → the concrete joint Gaussian integral of f(X) f(Y), with Y_i = s^(g_i) X_i + sqrt(1-s^(2g_i)) G_i and independent Gaussian X,G; reason: this is the source correlated pair; the equivalent spectral identity remains a proof obligation rather than a defining assumption
--   - encoding: the normalized halfspace Σ_i c_i X_i ≥ c₀, with Σ_i c_i² = 1 and only grade-one support → HasSum (fun i => c i²) 1, the L² sum gradeOneLinear c, and a.e. equality to its halfspace indicator; reason: Hilbert-space synthesis represents every square-summable Gaussian linear form; it avoids imposing absolute pointwise convergence or finite support
--   - encoding: H_a = (−∞, Φ⁻¹(a)) ⊂ ℝ → modelHalfspace a in Fin 1 → ℝ using the published Cohen2019.Robust.PhiInvReal; reason: the identical one-dimensional event and standard Gaussian quantile, evaluated only at 0 < a < 1
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma 4.3, p.14; §2, p.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Supplement_Noise

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussPolyReg.Approx.Supplement

/-- Lemma 4.3, p.14: no initial Boolean assumption, and no finite-support
restriction on the grade-one halfspace normal. -/
theorem lemma_4_3 (a s : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (f : GradedL2)
    (hf : ∀ᵐ x ∂gaussianProduct GradedIndex, 0 ≤ f x ∧ f x ≤ 1)
    (hmean : (∫ x, f x ∂gaussianProduct GradedIndex) = a)
    (hstab : noiseStability coordinateGrade s f = setStability s (modelHalfspace a)) :
    ∃ (c : ℕ → ℝ) (t : ℝ), HasSum (fun i => c i ^ 2) 1 ∧
      (f : GradedPoint → ℝ) =ᵐ[gaussianProduct GradedIndex]
        (gradeOneHalfspace c t).indicator (fun _ => (1 : ℝ)) := by sorry

end GaussPolyReg.Approx.Supplement
