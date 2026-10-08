-- Prove2me | Theorems.Thm_MFGLimit_LDP_lemma_6_4
-- name    : MFGLimit.LDP.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:58.861426+00:00
-- url     : https://prove2.me/theorems/072061fc-90da-42d1-9705-1945ae148800
-- title:
--   Lemma 6.4, p. 26 — for φ ∈ H¹₀, I^φ(ν) = Ĩ^φ((ν_t ∘ τ⁻¹_{φ_t})_{t∈[0,T]}) (6.7)
-- statement:
--   Assume Condition 6.3(2) on $\tilde b$. For every $\phi\in\mathcal H^1_0([0,T];\mathbb R^d)$ (absolutely continuous, square-integrable derivative, $\phi_0=0$) and every $\nu\in C([0,T];\mathcal P^1(\mathbb R^d))$,
--
--   $$I^\phi(\nu)=\tilde I^\phi\big((\nu_t\circ\tau_{\phi_t}^{-1})_{t\in[0,T]}\big), \qquad (6.7)$$
--
--   where $I^\phi$ is the action functional (6.4) with the extra transport term $\mathrm{div}(\nu_t\dot\phi_t)$ and $\tilde I^\phi$ is the action functional (6.6) for the shifted drift $\tilde b(t,x+\phi_t,m\circ\tau^{-1}_{-\phi_t})$.
--
--   The identity is what makes $I^\phi$ meaningful for merely continuous $\phi$ (p. 27).
--
--   **Formalization Note** $I^\phi$ for $\phi\in\mathcal H^1$ (`IphiH1`) and the extension for continuous $\phi$ (`Iphi`) are different definitions, so the lemma is not true by definition.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 26, Lemma 6.4, (6.7)

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_MeasureDeriv
import Definitions.Def_MFGLimit_LDP_Equations
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_MFGLimit_LDP_PathSpace
import Definitions.Def_MFGLimit_LDP_Action

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

/-- Lemma 6.4, p. 26 (the shifted action functional, (6.7)). -/
theorem lemma_6_4 {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℝ) (T : ℝ≥0) (hT : 0 < T)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d) (hb : DriftCond T btil)
    (φ : ℝ → MFGLimit.Conc.E d) (hφ : IsH1 T φ) (hφ0 : φ 0 = 0) (ν : PathP1 d T) :
    IphiH1 σ btil φ ν.ν = Itil σ btil φ (shiftFlow ν.ν φ) := by sorry

end MFGLimit.LDP
