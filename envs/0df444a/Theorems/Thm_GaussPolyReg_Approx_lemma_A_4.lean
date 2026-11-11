-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_A_4
-- name    : GaussPolyReg.Approx.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:27.884317+00:00
-- url     : https://prove2.me/theorems/b774ea69-002f-4c1b-8c5b-c049eb45b352
-- title:
--   Lemma A.4 — convergence in law implies moments and every Wᵣ convergence
-- statement:
--   Let $d_1,\ldots,d_k\in\mathbb N$ and $p_{n,i}\in H_{\le d_i}(X)$. Suppose $P_n=(p_{n,1},\ldots,p_{n,k})$ converges in distribution to an arbitrary real random vector $P$. All mixed moments are finite and converge, and for every real $r\ge1$,
--
--   $$\mathbb E\prod_i p_{n,i}^{a_i}\to\mathbb E\prod_i P_i^{a_i},\qquad W_r(\operatorname{Law}(P_n),\operatorname{Law}(P))\to0.$$
--
--   The same assertions hold for $p_{n,i}\in H_{d_i}^{\rm gr}(Z)$ on any index set of independent standard Gaussian variables with positive grades. The limit may be defined on any probability space. Both regimes and every finite Wasserstein exponent are included. This permits upgrading weak approximation to quantitative transport convergence.
--
--   Differences from the source:
--   - encoding: functions of the original Gaussian variables, with the closed spans fixed in §2 → L² almost-everywhere classes on the product Gaussian space indexed by ℕ; index n uses coordinates 0 through n−1; reason: reindexing X₁,X₂,… changes no random variable or closed-span instance
--   - encoding: convergence in distribution and convergence of all moments, including the graded case → filter atTop, arbitrary limit probability spaces, explicit monomial integrability and every real absolute moment, and MomentUpgrade; reason: makes finiteness explicit and expresses the conclusions proved on p.17; the arbitrary graded index set is retained
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma A.4, p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_MomentConvergence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem lemma_A_4 :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (k : ℕ) (d : Fin k → ℕ) (p : ℕ → Fin k → Original)
      (hp : ∀ n i, p n i ∈ chaosLE (d i)) (P : Fin k → Ω → ℝ),
      TendstoInDistribution (fun n => vectorOf (fun i x => p n i x)) atTop
        (vectorOf P) (fun _ => gaussianProduct ℕ) μ →
      MomentUpgrade (gaussianProduct ℕ) μ (fun n i x => p n i x) P) ∧
    (∀ {I Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : I → ℕ) (hg : ∀ i, 1 ≤ g i) (k : ℕ) (d : Fin k → ℕ)
      (p : ℕ → Fin k → GaussianL2 I)
      (hp : ∀ n i, p n i ∈ gradedChaos g (d i)) (P : Fin k → Ω → ℝ),
      TendstoInDistribution (fun n => vectorOf (fun i x => p n i x)) atTop
        (vectorOf P) (fun _ => gaussianProduct I) μ →
      MomentUpgrade (gaussianProduct I) μ (fun n i x => p n i x) P) := by sorry

end GaussPolyReg.Approx
