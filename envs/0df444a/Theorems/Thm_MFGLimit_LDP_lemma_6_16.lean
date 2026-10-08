-- Prove2me | Theorems.Thm_MFGLimit_LDP_lemma_6_16
-- name    : MFGLimit.LDP.lemma_6_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:46.815079+00:00
-- url     : https://prove2.me/theorems/078274e5-a458-4b6d-82f4-36e58e8d263a
-- title:
--   Lemma 6.16, p. 33 — the McKean–Vlasov map Φ is uniformly continuous from P¹(ℝ^d × C^d_0) × C^{d₀}_0 into C([0,T]; P¹(ℝ^d))
-- statement:
--   Assume Condition 6.3(2) on $\tilde b$ and that $\sigma$ is non-degenerate. Let $\Phi(\mathcal Q,\phi)$ be the flow of marginal laws of the solution of the McKean–Vlasov equation $x_t=e+\int_0^t\tilde b(s,x_s,\mathcal Q\circ x_s^{-1})ds+\sigma w_t+\sigma_0\phi_t$ of §6.3.2. Then $\Phi$ maps $\mathcal P^1(\mathbb R^d\times\mathcal C^d_0)\times\mathcal C^{d_0}_0$ into $C([0,T];\mathcal P^1(\mathbb R^d))$ and is uniformly continuous: for every $\varepsilon>0$ there is $\delta>0$ such that
--
--   $$\max\big(\mathcal W_1(\mathcal Q,\mathcal Q'),\|\phi-\phi'\|_\infty\big)<\delta\ \Longrightarrow\ \sup_{t\in[0,T]}\mathcal W_1\big([\Phi(\mathcal Q,\phi)]_t,[\Phi(\mathcal Q',\phi')]_t\big)<\varepsilon.$$
--
--   Uniform continuity is what allows the contraction principle to carry the relaxed upper bound of Proposition 6.15 to the empirical measure flows.
--
--   **Formalization Note** The solution map is a hypothesis satisfying the equation $\mathcal Q$-a.s. (the paper asserts unique solvability under Condition 6.3).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 33, Lemma 6.16

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_MeasureDeriv
import Definitions.Def_MFGLimit_LDP_Equations
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_MFGLimit_LDP_PathSpace
import Definitions.Def_MFGLimit_LDP_Action
import Definitions.Def_MFGLimit_LDP_Contraction

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

/-- Lemma 6.16, p. 33 (the McKean–Vlasov solution map `Φ` is uniformly continuous). -/
theorem lemma_6_16 {d d₀ : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hσ : σ.det ≠ 0) (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (hb : DriftCond T btil)
    (sol : Measure (MFGLimit.Conc.E d × C0T d T) → C0T d₀ T → MFGLimit.Conc.E d × C0T d T → CPath d T)
    (hsol : IsMVSolutionMap σ σ₀ btil sol) :
    (∀ z : QPhi d d₀ T, ∃ ν : PathP1 d T, ν.ν = PhiMap sol z) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z z' : QPhi d d₀ T, Dqp z z' < ENNReal.ofReal δ →
        (⨆ t, Wp 1 (PhiMap sol z t) (PhiMap sol z' t)) < ENNReal.ofReal ε := by sorry

end MFGLimit.LDP
