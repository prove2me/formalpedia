-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_theorem_V_1_part1
-- name    : NonuniformKuramoto.CondI.theorem_V_1_part1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:33.405171+00:00
-- url     : https://prove2.me/theorems/91355729-e993-4c9b-b06c-9e66857f097d
-- title:
--   Theorem V.1 1) — positively invariant $\bar\Delta(\gamma)$, $\gamma<\pi/2-\varphi_{\max}$, gives exponential frequency synchronization
-- statement:
--   Consider the non-uniform Kuramoto model (8) with $n\ge2$ oscillators, $D_i>0$, $P_{ij}\ge0$ and $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$, and $P_{ii}=\varphi_{ii}=0$; $P$ need be neither symmetric nor complete. Assume:
--
--   1. the graph induced by $P$ (edge $(i,j)$ iff $P_{ij}>0$) has a globally reachable node;
--   2. there is $\gamma\in[0,\pi/2-\varphi_{\max}[$ such that $\bar\Delta(\gamma)$ is positively invariant for (8).
--
--   Then every solution $\theta$ with $\theta(0)\in\bar\Delta(\gamma)$ achieves exponential frequency synchronization: there are $\dot\theta_\infty\in\mathbb R$, $C\in\mathbb R$ and $\lambda>0$ with
--
--   $$|\dot\theta_i(t)-\dot\theta_\infty|\le C e^{-\lambda t}\quad\text{for all } t\ge0,\ i\in\{1,\dots,n\},$$
--
--   and $\dot\theta_\infty\in[\dot\theta_{\min}(0),\dot\theta_{\max}(0)]$, the range of the initial frequencies.
--
--   Phase cohesiveness of the oscillators thus implies frequency synchronization; Theorem V.3 supplies the cohesiveness.
--
--   **Formalization Note** $\bar\Delta(\gamma)$ is stated on real lifts (all pairwise differences at most $\gamma$). The positive-invariance hypothesis quantifies over all solutions of (8), not only the solution in the conclusion. The range condition is written as $\exists i:\dot\theta_i(0)\le\dot\theta_\infty$ and $\exists i:\dot\theta_\infty\le\dot\theta_i(0)$.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 16, Theorem V.1 1)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Theorem V.1 1), p. 16: if the graph induced by `P` has a globally reachable node and `∆̄(γ)` is
positively invariant for some `γ ∈ [0, π/2 − ϕ_max[`, then every solution with `θ(0) ∈ ∆̄(γ)` achieves
exponential frequency synchronization to some `θ̇_∞ ∈ [θ̇_min(0), θ̇_max(0)]`. -/
theorem theorem_V_1_part1 {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 ≤ P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (hreach : HasGloballyReachableNode P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < Real.pi / 2 - phiMax ϕ)
    (hinv : IsPosInvariant D ω P ϕ (ArcClosed γ))
    (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ) (h0 : ArcClosed γ (θ 0)) :
    ∃ ωinf C r : ℝ, 0 < r ∧
      (∃ i, field D ω P ϕ (θ 0) i ≤ ωinf) ∧ (∃ i, ωinf ≤ field D ω P ϕ (θ 0) i) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ i, |field D ω P ϕ (θ t) i - ωinf| ≤ C * Real.exp (-r * t) := by sorry

end NonuniformKuramoto.CondI
