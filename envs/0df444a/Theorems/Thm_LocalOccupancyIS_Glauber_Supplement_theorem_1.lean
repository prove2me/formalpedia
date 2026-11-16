-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_Supplement_theorem_1
-- name    : LocalOccupancyIS.Glauber.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:01:18.898334+00:00
-- url     : https://prove2.me/theorems/47b54b45-b2c8-48b0-8a23-a652d53258d7
-- title:
--   Theorem 1 — neighborhood block dynamics
-- statement:
--   Let $G$ be a nonempty finite simple graph on $n$ vertices with degree at most $\Delta$, and suppose it has local occupancy parameters $(\lambda,\beta,\gamma)$, all positive. Put $\Gamma=\beta+\gamma\Delta$, $H_0=D_{\rm KL}(\nu_0\|\mu_{G,\lambda})$ in nats, and $H_\lambda=n\log((1+\lambda)/\min\{1,\lambda\})$. From every initial probability law $\nu_0$, for every integer $T\ge1$ and independent uniform $J\in\{0,\ldots,T-1\}$, neighborhood block dynamics satisfies
--
--   $$\mathbb E|I_J|\ge\frac n\Gamma\left(1-\sqrt{\frac{(\beta^2+\gamma^2\Delta^2)H_0}{2T}}\right).$$
--
--   For every $0<\epsilon<1$, the threshold $T\ge(\beta^2+\gamma^2\Delta^2)H_\lambda/(2\epsilon^2)$ gives $\mathbb E|I_J|\ge(1-\epsilon)n/\Gamma$. The block kernel is stochastic. Enumerating the neighborhood assignments implements $Q_u$ exactly, the table has positive total weight, and the local counter update preserves the counters. There are absolute constants $C,c>0$, chosen before every graph and fugacity, such that each enumerated block update costs at most $Ce^{c\Delta}$ charged operations, including degree zero.
--
--   This gives the occupancy guarantee without rapid mixing or reversibility hypotheses. The cost model uses exact real arithmetic and exact finite random choice; it asserts no bit-cost bound for arbitrary real inputs.
--
--   Differences from the source:
--   - encoding: uniform random choice of a vertex in a finite graph → an explicit Nonempty vertex-type instance; reason: the source dynamics require at least one vertex for uniform site selection, while edgeless nonempty graphs remain allowed
--   - encoding: the random time and the statement that a block can be enumerated in time 2^{O(Δ)} → the finite time mean, an explicit enumerated kernel, maintained-counter update and charged traces with an absolute exponential bound; reason: these specify the process and source arithmetic/random-choice convention without assuming its guarantee
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), p.4, Theorem 1, equation (3); proof §3 pp.12–13

import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_BlockDynamics
import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_MadParameters

namespace LocalOccupancyIS.Glauber.Supplement
/-- Theorem 1, p.4, including the enumerated block implementation.
C and c are absolute; exact-real arithmetic and exact weighted choice are charged primitives. -/
theorem theorem_1 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), RealDegreeBound G Δ →
    ∀ lam β γ : ℝ, 0 < lam → LocalOccupancy G lam β γ →
      MarkovMixing.IsStochastic (blockKernel G lam) ∧
      (∀ u, enumerationQ G lam u = Q G lam u ∧
        (∀ σ : State G, 0 < tableMass G lam u σ (counters G σ)) ∧
        (∀ (σ τ : State G),
          (∀ v ∉ insert u (G.neighborFinset u), τ.val v = σ.val v) →
          maintainedCounts G u σ τ (counters G σ) = counters G τ) ∧
        (blockWork G u : ℝ) ≤ C * Real.exp (c * Δ)) ∧
      ∀ ν : State G → ℝ, MarkovMixing.IsDist ν →
        let H₀ := kl ν (HardCoreBochner.hcLaw G lam)
        let Hlam := entropyBound (Fintype.card V) lam
        let Γ := β + γ * Δ
        ∀ T : ℕ, 1 ≤ T →
          blockMean G lam ν T ≥ Fintype.card V / Γ *
            (1 - Real.sqrt ((β^2 + γ^2 * (Δ : ℝ)^2) * H₀ / (2*T))) ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            (β^2 + γ^2 * (Δ : ℝ)^2) * Hlam / (2*ε^2) ≤ T →
            blockMean G lam ν T ≥ (1-ε) * Fintype.card V / Γ := by sorry
end LocalOccupancyIS.Glauber.Supplement
