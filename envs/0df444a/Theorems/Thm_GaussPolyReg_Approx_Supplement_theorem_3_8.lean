-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_Supplement_theorem_3_8
-- name    : GaussPolyReg.Approx.Supplement.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:27:10.596357+00:00
-- url     : https://prove2.me/theorems/08f8d92e-23f2-4033-8feb-33a93efe1112
-- title:
--   Theorem 3.8 — countable joint compactification and finite joint-law compactness
-- statement:
--   Let $Z$ have countably many independent standard Gaussian variables of each positive grade. For every degree sequence $d_k\in\mathbb N$ and every $p_{n,k}\in H_{d_k}^{\mathrm{gr}}(Z)$ such that $\sup_n\mathbb E p_{n,k}^2<\infty$ for each $k$, there are a strictly increasing subsequence $\phi$ and $P_k\in H_{d_k}^{\mathrm{gr}}(Z)$ with
--
--   $$(p_{\phi(n),k})_{k\in\mathbb N}\xrightarrow{d}(P_k)_{k\in\mathbb N}.$$
--
--   In addition, for every finite $k$ and every degree vector $(d_i)_{i<k}$,
--
--   $$\{\operatorname{Law}(P_1,\ldots,P_k):P_i\in H_{d_i}^{\mathrm{gr}}(Z),\ \mathbb E P_i^2\le1\text{ for every }i\}\quad\text{is weakly compact}.$$
--
--   Both assertions are included in a single conjunction. The bounds can differ with $k$, there is one subsequence for the whole countable family, and the finite joint-law set permits dependence. The already published Open `GrothendieckPD.Digits.theorem_3_2` supplies the countable subsequence assertion for use in a proof; the present target also retains the explicit finite joint-law compactness conclusion.
--
--   Differences from the source:
--   - encoding: closed Hermite chaos on countably many independent Gaussian variables of every positive grade → the published L² closed spans on I = ℕ+ × ℕ with grade (r,i) = r; reason: a fixed reindexing of exactly the source space, with a.e. classes and degree zero retained
--   - encoding: joint convergence in distribution on ℝ^ℕ with its product topology → convergence of expectations of every bounded continuous test on ℕ → ℝ, along a strictly increasing map φ : ℕ → ℕ; reason: the definition of weak convergence of the joint laws, and strict increase ensures a subsequence tending to infinity
--   - encoding: sup_n E p²_{n,k} < ∞ for each k → for each k there exists a real B with ‖p n k‖² ≤ B for every n; reason: equivalent coordinatewise L² boundedness, with no real supremum default
--   - encoding: weak compactness of each finite joint-law set with coordinatewise second moments at most one → IsCompact of boundedJointLaws d in ProbabilityMeasure (Vec k), with underlying measure vectorLaw p; reason: the published Euclidean joint-law interface gives precisely the same joint-law set and the standard weak topology
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Theorem 3.8, p.11; §2, p.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Supplement_Graded

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussPolyReg.Approx.Supplement

/-- Theorem 3.8, p.11: the whole countable subsequence assertion and finite
joint-law compactness. Includes degree zero and separately bounded coordinates. -/
theorem theorem_3_8 :
    (∀ (d : ℕ → ℕ) (p : ℕ → ℕ → GradedL2),
      (∀ n k, p n k ∈ gradedChaos coordinateGrade (d k)) →
      (∀ k, ∃ B : ℝ, ∀ n, ‖p n k‖ ^ 2 ≤ B) →
      ∃ (φ : ℕ → ℕ) (P : ℕ → GradedL2), StrictMono φ ∧
        (∀ k, P k ∈ gradedChaos coordinateGrade (d k)) ∧
        ∀ F : BoundedContinuousFunction (ℕ → ℝ) ℝ,
          Tendsto (fun n => ∫ x, F (fun k => p (φ n) k x) ∂gaussianProduct GradedIndex)
            atTop (𝓝 (∫ x, F (fun k => P k x) ∂gaussianProduct GradedIndex))) ∧
    (∀ (k : ℕ) (d : Fin k → ℕ), IsCompact (boundedJointLaws d)) := by sorry

end GaussPolyReg.Approx.Supplement
