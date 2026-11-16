-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_Supplement_theorem_8
-- name    : LocalOccupancyIS.Glauber.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:01:54.708674+00:00
-- url     : https://prove2.me/theorems/61fc3a38-c31a-4f4c-a53e-169146e3d724
-- title:
--   Theorem 8 — exact one sweep and bounded local mad
-- statement:
--   Let $G$ be a nonempty finite simple graph with degree at most $\Delta$ and let $\lambda>0$.
--
--   1. If $G$ is triangle free, any deterministic full sweep of $N(u)$ equals $Q_u$ as a kernel, for every center. For any valid local occupancy parameters $(\lambda,\beta,\gamma)$, these sweeps satisfy the certificate with $\eta=0$ and occurrence bound $\kappa\le\Delta$. With $\Gamma=\beta+\gamma\Delta$ and $C_1=\beta+\Delta\max\{\beta p,\gamma\Delta\}$, from every initial probability law the full Theorem 2 consequence is
--
--   $$\mathbb E|I_J|\ge\frac n\Gamma\left(1-C_1\sqrt{\frac{H_0}{2T}}\right).$$
--
--   Its threshold $T\ge C_1^2H_\lambda/(2\epsilon^2)$ yields $(1-\epsilon)n/\Gamma$, for $T\ge1$ and $0<\epsilon<1$.
--
--   2. For $\Delta\ge1$ and $a\ge0$, if every neighborhood has maximum average degree at most $a$, the computed equation (19) parameters give local occupancy and
--
--   $$\Gamma=\beta_{19}+\gamma_{19}\Delta=\frac{e^w}{p}=\frac{\Delta(1+\lambda)^a\log(1+\lambda)}{pW(\Delta(1+\lambda)^a\log(1+\lambda))}.$$
--
--   Any two full neighborhood sweeps, whose deterministic orders may differ, satisfy the same certificate with $\eta=0$ and $\kappa\le2\Delta$. From every initial state,
--
--   $$T\ge\frac{(\beta_{19}+2\Delta\max\{\beta_{19}p,\gamma_{19}\Delta\})^2H_\lambda}{2\epsilon^2}\quad\Longrightarrow\quad\mathbb E|I_J|\ge\frac{(1-\epsilon)n}{\Gamma}.$$
--
--   Here $J$ is independent and uniform on the first $T$ times. The result includes edgeless neighborhoods and all positive fugacities; the parameters and certificate are conclusions, not supplied guarantees.
--
--   Differences from the source:
--   - encoding: uniform random choice of a vertex in a finite graph → an explicit Nonempty vertex-type instance; reason: the source dynamics require at least one vertex for uniform site selection, while edgeless nonempty graphs remain allowed
--   - encoding: local maximum average degree at most a, arbitrary feasible exteriors, and uniform random time → HereditaryDensity G 1 a, equality of full state-space kernels, and the finite time mean; reason: t=1 density is precisely induced average degree; kernel equality includes every feasible exterior and state
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), p.15, Theorem 8 and equations (19)–(20); proof pp.16–17

import Definitions.Def_LocalOccupancyIS_Glauber_Supplement_MadParameters

namespace LocalOccupancyIS.Glauber.Supplement
/-- Theorem 8(a),(b), pp.15–17. Sweep orders are deterministic and may differ.
HereditaryDensity G 1 a is exactly the source's local maximum average degree bound. -/
theorem theorem_8 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ lam : ℝ)
    (hdeg : RealDegreeBound G Δ) (hlam : 0 < lam) :
    (TriangleFree G →
      (∀ (u : V) (w : List V), IsSweep (G.neighborFinset u) w →
        word G lam w = Q G lam u) ∧
      ∀ β γ : ℝ, LocalOccupancy G lam β γ →
        ∀ w : V → List V, (∀ u, IsSweep (G.neighborFinset u) (w u)) →
          WordCertificate G lam β γ 0 w ∧ (occurrences w : ℝ) ≤ Δ ∧
          ∀ ν : State G → ℝ, MarkovMixing.IsDist ν →
            let C₁ := β + Δ * max (β * p lam) (γ * Δ)
            let Γ := β + γ * Δ
            ∀ T : ℕ, 1 ≤ T →
              timeMean G lam ν T ≥ Fintype.card V / Γ *
                (1 - C₁ * Real.sqrt (kl ν (HardCoreBochner.hcLaw G lam) / (2*T))) ∧
              ∀ ε : ℝ, 0 < ε → ε < 1 →
                C₁^2 * entropyBound (Fintype.card V) lam / (2*ε^2) ≤ T →
                timeMean G lam ν T ≥ (1-ε) * Fintype.card V / Γ) ∧
    (1 ≤ Δ → ∀ a : ℝ, 0 ≤ a → HereditaryDensity G 1 a →
      let β := madBeta Δ a lam
      let γ := madGamma Δ a lam
      let w₀ := madW Δ a lam
      LocalOccupancy G lam β γ ∧
      β + γ * Δ = Real.exp w₀ / p lam ∧
      β + γ * Δ = Δ * (1+lam)^a * Real.log (1+lam) / (p lam * w₀) ∧
      ∀ w₁ w₂ : V → List V,
        (∀ u, IsSweep (G.neighborFinset u) (w₁ u)) →
        (∀ u, IsSweep (G.neighborFinset u) (w₂ u)) →
        WordCertificate G lam β γ 0 (fun u => w₁ u ++ w₂ u) ∧
        (occurrences (fun u => w₁ u ++ w₂ u) : ℝ) ≤ 2*Δ ∧
        ∀ (σ : State G) (T : ℕ), 1 ≤ T →
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            (β + 2*Δ * max (β * p lam) (γ * Δ))^2 *
              entropyBound (Fintype.card V) lam / (2*ε^2) ≤ T →
            timeMean G lam (point σ) T ≥
              (1-ε) * Fintype.card V / (β + γ * Δ)) := by sorry
end LocalOccupancyIS.Glauber.Supplement
