-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_Supplement_theorem_10_1
-- name    : HypergraphUnreliability.FPRAS.Supplement.theorem_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:17.678201+00:00
-- url     : https://prove2.me/theorems/24675e81-a85a-43d2-a9cf-14815189a310
-- title:
--   Theorem 10.1 — Surviving-witness importance sampler is unbiased with bounded relative second moment
-- statement:
--   Let $P$ be a continuous-time Markov chain on a finite state space $S$ with nonnegative off-diagonal rates $q$, observed until time $T\ge0$. Let $\mathcal W$ be a finite set of $M\ge1$ witnesses with alive sets $\mathcal W(x)$, such that no witness revives along a positive-rate jump, and let the chain start from an initial distribution $\mu$ supported on states where all witnesses are alive. Let $\mathcal E=\{\mathcal W(X_T)\ne\emptyset\}$. For each $w\in\mathcal W$ let $Q_w$ be the chain in which exactly the transitions destroying $w$ are suppressed and all other rates retained, let $k_w(x)$ be the total suppressed rate, and, choosing $w$ uniformly and sampling $X\sim Q_w$ from $\mu$, put
--   $$W=\frac{M}{|\mathcal W(X_T)|}\exp\Bigl(-\int_0^T k_w(X_t)\,dt\Bigr).\tag{10.1}$$
--   Then:
--
--   1. $\mathbb E W=\mathbb P_P(\mathcal E)$.
--   2. For every real $A_0$: if every path of every $Q_w$ from a state of positive initial probability satisfies $\int_0^T k_w(X_t)\,dt\ge A_0$, then on every such path $0\le W\le Me^{-A_0}$, and, whenever $\mathbb P_P(\mathcal E)>0$,
--   $$\frac{\mathbb E W^2}{\mathbb P_P(\mathcal E)^2}\le\frac{Me^{-A_0}}{\mathbb P_P(\mathcal E)}.$$
--
--   This is the general path-weighting identity behind the hypergraph estimator: in the application the witnesses are representative pairs and the paired-head hazard bound supplies $A_0=\lambda T$. It is a companion theorem of the mission and is not used in the proof of the goal.
--
--   **Formalization Note** The objects are those of the definition `HypergraphUnreliability_FPRAS_Supplement_WitnessSystem`. A path of $Q_w$ is a path with ordered jump times in $(0,T)$, starting at the given state, all of whose jumps have positive $Q_w$ rate. $\mathbb E W^2$ is $\mathbb E[W^2]$.
--
--   Differences from the source:
--   - generalization: a chain started from an (unspecified) initial state with all witnesses alive → an arbitrary initial probability distribution supported on states with all witnesses alive, shared by $P$ and every $Q_w$; reason: a fixed initial state is the Dirac special case, so the Lean statement specializes to the source's
--   - encoding: bounded rates → nonnegative real off-diagonal rates on a finite state space; reason: finitely many real rates are bounded, so the instances are the same
--   - encoding: observed until time $T$ → a real $T$ with $0\le T$; reason: an observation horizon is a nonnegative time
--   - encoding: "every suppressed path" and the range of the random variable $W$ → every path of every $Q_w$ from a state of positive initial probability; reason: these are exactly the paths of the sampled proposal process
--   - encoding: $W$ undefined where no witness survives → $W:=0$ there; reason: such paths have no $Q_w$-probability and never occur as proposal paths
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Theorem 10.1, p. 16 (proof p. 16)

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_JumpChain
import Definitions.Def_HypergraphUnreliability_FPRAS_Supplement_WitnessSystem

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS.Supplement

open WitnessSystem

/-- Theorem 10.1, p. 16. For a finite surviving-witness system with `M = |𝒲| ≥ 1` and horizon
`T ≥ 0`: `E W = P_P(𝓔)`; and if every path of every `Q_w` from an allowed initial state has
`∫₀^T k_w(X_t) dt ≥ A₀`, then `0 ≤ W ≤ M e^{-A₀}` on each such path and, when `P_P(𝓔) > 0`,
`E W² / P_P(𝓔)² ≤ M e^{-A₀} / P_P(𝓔)`. -/
theorem theorem_10_1 {S 𝒲 : Type} [Fintype S] [Fintype 𝒲] [Nonempty 𝒲]
    (sys : WitnessSystem S 𝒲) (hsys : sys.IsValid) (T : ℝ) (hT : 0 ≤ T) :
    sys.estimatorMean T = sys.survivalProb T ∧
      ∀ A₀ : ℝ,
        (∀ (w : 𝒲) (x₀ : S), 0 < sys.init x₀ → ∀ π : JumpPath S,
            IsChainPath (sys.suppressedRate w) x₀ T π →
              A₀ ≤ JumpPath.pathIntegral (sys.killRate w) T π) →
          (∀ (w : 𝒲) (x₀ : S), 0 < sys.init x₀ → ∀ π : JumpPath S,
              IsChainPath (sys.suppressedRate w) x₀ T π →
                0 ≤ sys.estimator T w π ∧
                  sys.estimator T w π ≤ (Fintype.card 𝒲 : ℝ) * Real.exp (-A₀)) ∧
            (0 < sys.survivalProb T →
              sys.estimatorSecondMoment T / sys.survivalProb T ^ 2 ≤
                (Fintype.card 𝒲 : ℝ) * Real.exp (-A₀) / sys.survivalProb T) := by sorry

end HypergraphUnreliability.FPRAS.Supplement
