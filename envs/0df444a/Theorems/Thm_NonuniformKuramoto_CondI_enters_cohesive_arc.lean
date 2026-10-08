-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_enters_cohesive_arc
-- name    : NonuniformKuramoto.CondI.enters_cohesive_arc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:11.515365+00:00
-- url     : https://prove2.me/theorems/719fe807-38c4-49b5-bdeb-7a7f86423000
-- title:
--   Proof of Theorem V.3, p. 22 — from $\Delta(\gamma_{\max})$, $\theta(t)\in\bar\Delta(\pi/2-\varphi_{\max})$ for all $t\ge T$
-- statement:
--   Under the hypotheses of Theorem V.3 (model (8) with $n\ge2$, $D_i>0$, $P_{ij}=P_{ji}>0$ for $i\ne j$, $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$, $P_{ii}=\varphi_{ii}=0$, and condition (26)), every solution $\theta$ of (8) with $\theta(0)\in\Delta(\gamma_{\max})$ eventually enters and stays in the cohesive set $\bar\Delta(\pi/2-\varphi_{\max})$: there is $T\ge0$ with
--
--   $$\theta(t)\in\bar\Delta(\pi/2-\varphi_{\max})\qquad\text{for all }t\ge T.$$
--
--   From time $T$ on, the positive-invariance hypothesis of Theorem V.1 is satisfied, which yields frequency synchronization.
--
--   **Formalization Note** $\Delta(\gamma_{\max})$ and $\bar\Delta(\pi/2-\varphi_{\max})$ are stated on the same continuous real lift of the solution (strict, resp. non-strict, bounds on all pairwise differences).
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 22, proof of Theorem V.3, penultimate sentence

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Proof of Theorem V.3, p. 22: under (26), with `P = Pᵀ` complete, for every solution with
`θ(0) ∈ ∆(γ_max)` there is `T ≥ 0` with `θ(t) ∈ ∆̄(π/2 − ϕ_max)` for all `t ≥ T`. -/
theorem enters_cohesive_arc {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hPsymm : ∀ i j, P i j = P j i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ)
    (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ) (h0 : ArcOpen (gammaMax D ω P ϕ) (θ 0)) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ArcClosed (Real.pi / 2 - phiMax ϕ) (θ t) := by sorry

end NonuniformKuramoto.CondI
