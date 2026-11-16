-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_Supplement_lemma_4_2
-- name    : GaussPolyReg.Approx.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:27:47.307456+00:00
-- url     : https://prove2.me/theorems/0b0ca1b4-ba69-4b83-9efb-9b9152f50117
-- title:
--   Lemma 4.2 — a common graded indicator limit and all noise stabilities
-- statement:
--   Let $a\in[0,1]$ and let $A_n\subset\mathbb R^{n+1}$ be Gaussian-measurable sets with $\gamma_{n+1}(A_n)=a$. There exist a strictly increasing $\phi:\mathbb N\to\mathbb N$ and $f\in L^2(Z)$ on the countable graded Gaussian space such that
--
--   $$0\le f\le1\quad\text{a.e.},\qquad \mathbb Ef=a,\qquad
--   (\Pi_k\mathbf1_{A_{\phi(n)}})_{k\in\mathbb N}\xrightarrow{d}(\Pi_k f)_{k\in\mathbb N},$$
--
--   and, for every $s\in(0,1)$ along this same subsequence,
--
--   $$\operatorname{Stab}_s(A_{\phi(n)})\longrightarrow\operatorname{Stab}_s(f).$$
--
--   The ordinary components on the left use grade-one Gaussian coordinates; those on the right use total graded degree. The endpoints $a=0$ and $a=1$ remain allowed. The subsequence and the limit are chosen before $s$. This supplies the compact limit needed for the robust Borell theorem without assuming that the limit is initially an indicator.
--
--   Differences from the source:
--   - encoding: closed Hermite chaos on countably many independent Gaussian variables of every positive grade → the published L² closed spans on I = ℕ+ × ℕ with grade (r,i) = r; reason: a fixed reindexing of exactly the source space, with a.e. classes and degree zero retained
--   - encoding: Gaussian-measurable sets, indicators and expectations → NullMeasurableSet for the Gaussian measure, L² indicator classes and real Gaussian probabilities; reason: includes the completion of the measure and all source events; bounded indicators and L² functions on probability spaces are integrable
--   - encoding: joint convergence in distribution on ℝ^ℕ with its product topology → convergence of expectations of every bounded continuous test on ℕ → ℝ, along a strictly increasing map φ : ℕ → ℕ; reason: the definition of weak convergence of the joint laws, and strict increase ensures a subsequence tending to infinity
--   - encoding: OU noise stability with correlation s on ordinary coordinates and s^r on grade-r coordinates → the concrete joint Gaussian integral of f(X) f(Y), with Y_i = s^(g_i) X_i + sqrt(1-s^(2g_i)) G_i and independent Gaussian X,G; reason: this is the source correlated pair; the equivalent spectral identity remains a proof obligation rather than a defining assumption
--   - encoding: a sequence of sets A_n ⊂ ℝ^n in the positive dimensions → A n ⊂ ℝ^(n+1) for n : ℕ; reason: enumerates all positive dimensions; demanding a dimension-zero set of measure a in (0,1) would spuriously make the input impossible
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma 4.2, p.13; §2, p.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Supplement_Noise

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussPolyReg.Approx.Supplement

/-- Lemma 4.2, p.13. Dimensions n+1 enumerate the positive dimensions, so
no spurious dimension-zero event of intermediate measure is required. -/
theorem lemma_4_2 (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (A : (n : ℕ) → Set (Fin (n + 1) → ℝ))
    (hA : ∀ n, NullMeasurableSet (A n) (gaussianProduct (Fin (n + 1))))
    (hmass : ∀ n, gaussianMass (A n) = a) :
    ∃ (φ : ℕ → ℕ) (f : GradedL2), StrictMono φ ∧
      (∀ᵐ x ∂gaussianProduct GradedIndex, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∫ x, f x ∂gaussianProduct GradedIndex) = a ∧
      (∀ F : BoundedContinuousFunction (ℕ → ℝ) ℝ,
        Tendsto (fun n => ∫ x,
          F (fun k => gradedProjection (fun _ => 1) k (indicatorL2 (A (φ n))) x)
            ∂gaussianProduct (Fin (φ n + 1))) atTop
          (𝓝 (∫ x, F (fun k => gradedProjection coordinateGrade k f x)
            ∂gaussianProduct GradedIndex))) ∧
      (∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 →
        Tendsto (fun n => setStability s (A (φ n))) atTop
          (𝓝 (noiseStability coordinateGrade s f))) := by sorry

end GaussPolyReg.Approx.Supplement
