-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_theorem_1_2
-- name    : KSATSingleFlip.Connect.theorem_1_2
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T07:14:04.26448+00:00
-- url     : https://prove2.me/theorems/eea0a702-3ae8-4372-a6c6-8692b6fad173
-- title:
--   Theorem 1.2 — Reconstruction onset
-- statement:
--   For fixed $k$ and $\alpha$, let $R_k(\alpha)$ be the reconstruction signal obtained by taking first $\limsup_{n\to\infty}$ and then the limit as $r\to\infty$. The outer limit exists. For all sufficiently large $k$, non-reconstruction holds throughout (1.2):
--   $$0\le\alpha\le\frac{2^k}{k}\left(\ln k+\ln\ln k+\gamma_*-(\ln\ln k)^{-1/16}\right).$$
--   For every $\varepsilon>0$ and sufficiently large $k$, reconstruction holds throughout
--   $$\frac{2^k}{k}(\ln k+\ln\ln k+\gamma_*+\varepsilon)\le\alpha\le2^k\left(\ln2-\frac1{\ln k}\right).$$
--   At each fixed $r\ge1$, the formula and the sampled exterior predict the root with expected error at most $C/(k\ln k)+o_n(1)$, with an absolute $C$ and the error uniform in $\alpha$ over this interval. Consequently the first reconstruction onset among satisfiable-with-high-probability densities satisfies
--   $$\alpha_{\rm clust}(k)=\frac{2^k}{k}(\ln k+\ln\ln k+\gamma_*+o_k(1)).$$
--   The formal statement spells out the error limit and its quantifiers. The rate uses a limit operator, and its convergence is stated explicitly; no density-monotonicity assumption is made.
-- source:
--   Chunyang Wang, Yitong Yin, Yixiao Yu, Yiyao Zhang, Single-Variable Connectivity in Random k-SAT, Theorem 1.2 and preceding definition, printed p. 3 (PDF p. 5) of STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_ReconstructionThreshold
import Definitions.Def_KSATSingleFlip_Connect_SoftField

open scoped Classical BigOperators
open Filter Topology

namespace KSATSingleFlip.Connect

/-- Theorem 1.2: the reconstruction onset and prediction error. -/
theorem theorem_1_2 :
    (∀ k : ℕ, 2 ≤ k → ∀ α : ℝ, 0 ≤ α →
      Tendsto (reconstructionProfile k α) atTop (𝓝 (reconstructionRate k α))) ∧
    (∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ α : ℝ, 0 ≤ α → α ≤ densityBound k gammaStar →
      reconstructionRate k α = 0) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (∀ α : ℝ, 0 ≤ α →
        ((2 : ℝ) ^ k / k) * (Real.log k + Real.log (Real.log k) + gammaStar + ε) ≤ α →
        α ≤ (2 : ℝ) ^ k * (Real.log 2 - 1 / Real.log k) →
        0 < reconstructionRate k α) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ α : ℝ,
        0 ≤ α →
        ((2 : ℝ) ^ k / k) * (Real.log k + Real.log (Real.log k) + gammaStar + ε) ≤ α →
        α ≤ (2 : ℝ) ^ k * (Real.log 2 - 1 / Real.log k) →
        expectedReconstructionError k n α r ≤ C / ((k : ℝ) * Real.log k) + δ)) ∧
    Tendsto (fun k : ℕ => ((k : ℝ) / (2 : ℝ) ^ k) * reconstructionThreshold k -
      Real.log k - Real.log (Real.log k) - gammaStar) atTop (𝓝 0) := by
  sorry

end KSATSingleFlip.Connect
