-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_Supplement_theorem_1
-- name    : LargeCongestion.Poisson.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:31:56.725163+00:00
-- url     : https://prove2.me/theorems/8384bd5e-3e86-4965-8823-69dce8358630
-- title:
--   Theorem 1 — weighted mixed Nash equilibria converge to deterministic Wardrop flow-load limits
-- statement:
--   Let $E,T$ and $S_t$ be the fixed finite congestion structure, with continuous, nonnegative, weakly increasing resource costs $C_e$ on nonnegative real loads. In game $n$, players have types $\tau_i^n$, positive masses $w_i^n$, and independent mixed Nash strategies $\hat\sigma_i^n$. Suppose (12) holds: player counts diverge, maximum mass tends to zero, and the per-type sums of masses tend to demands $d_t$.
--
--   The sequence of induced expected flow-load vectors $(\hat y^n,\hat x^n)$ is bounded. For every subsequence converging to $(\hat y,\hat x)$,
--   $$ (\hat y,\hat x)\in\operatorname{WE}(\Gamma^\infty),\qquad (Y^n,X^n)\Rightarrow(\hat y,\hat x)\quad\text{along that subsequence}.$$
--   Here $\Gamma^\infty$ has the same costs and strategy families and demands $d$. The convergence concerns the full random flow-load vector. No positive lower bound on limiting demands, strict monotonicity of costs, equal weights or symmetry of finite players is imposed.
--
--   This companion result identifies the deterministic nonatomic limit of weighted games, alongside the published Bernoulli-to-Poisson goal.
--
--   Differences from the source:
--   - reading: printed blackboard N glyphs in weighted costs and weights (pp. 9–10) → positive real weights and nonnegative continuous real-load costs; reason: (12) requires positive weights tending to zero, and the continuous derivatives in Section 6 use real loads
--   - encoding: finite players and resource-subset mixed strategies → players Fin N and probability vectors on Finset E, zero off S_t; reason: enumeration changes no finite game; nonempty strategy families are the standing strategy-existence convention
--   - encoding: every accumulation point and convergent subsequence → limits along every strictly increasing map from natural numbers; reason: the vectors are finite dimensional, so this is exactly the sequential accumulation-point criterion
--   - encoding: convergence in distribution of the full vector to a constant → expectations converge for every bounded continuous real test function of all flow and load coordinates; reason: this is the weak convergence criterion on a finite-dimensional real space, not coordinatewise convergence alone
--   - encoding: maximum weight → the published finite real supremum, zero for no players; reason: finite nonempty games have the usual maximum; the empty game convention only affects an initial finite segment in (12)
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, Theorem 1, p. 13

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_Weighted

namespace LargeCongestion.Poisson.Supplement
open Filter
open scoped Topology

theorem theorem_1 {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (C : E → ℝ → ℝ)
    (hS : StrategiesNonempty S) (hC : ContinuousCosts C)
    (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (w : ∀ n, Fin (N n) → ℝ)
    (hw : ∀ n i, 0 < w n i) (d : T → ℝ) (h12 : Condition12 N τ w d)
    (σ : ∀ n, Fin (N n) → Finset E → ℝ)
    (heq : ∀ n, (WeightedGame.mk S C (τ n) (w n)).IsMNE (σ n)) :
    Bornology.IsBounded (Set.range (fun n => wMeanPair S (τ n) (w n) (σ n))) ∧
    ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ v : FlowLoad S,
      Tendsto (fun n => wMeanPair S (τ (φ n)) (w (φ n)) (σ (φ n))) atTop (𝓝 v) →
      IsWardrop S C d (extendFlow S v.1) v.2 ∧
      ∀ f : FlowLoad S → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
        Tendsto (fun n => wExpect (σ (φ n))
          (fun a => f (wRandomPair S (τ (φ n)) (w (φ n)) a))) atTop (𝓝 (f v)) := by sorry

end LargeCongestion.Poisson.Supplement
