-- Prove2me | Theorems.Thm_ImpulsiveISS_SmallGain_flow_decrease_4_12
-- name    : ImpulsiveISS.SmallGain.flow_decrease_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:35.931748+00:00
-- url     : https://prove2.me/theorems/5ee6f055-45c6-4f8d-bb0f-91da29bfd637
-- title:
--   Proof of Theorem 8, p. 19, (4.12) — off the origin, $V(x)\ge\chi(\|\xi\|)$ implies $\dot V_u(x)\le-\varphi(V(x))$ for some $\varphi\in\mathcal P$
-- statement:
--   Consider an interconnection of $n$ impulsive subsystems on $X=X_1\times\dots\times X_n$ with transition map $\phi_c$ and jump map $g$, satisfying the standing assumptions. Let $V_i$ be ISS-Lyapunov functions for the subsystems with gains $\chi_{ij}$, $\chi_i$ and rates $\varphi_i,\alpha_i$ as in (4.4)–(4.6), let the gain operator $\Gamma$ of (4.7) satisfy the small-gain condition (4.9), and let $\sigma$ be an $\Omega$-path for $\Gamma$. Put
--   $$V(x)=\max_i\sigma_i^{-1}(V_i(x_i)),\qquad \chi(r)=\max_i\sigma_i^{-1}(\chi_i(r)).$$
--
--   Then there is a positive definite $\varphi:\mathbb R_+\to\mathbb R_+$ such that for every $x\in X$ with $x\ne0$, every $\xi\in U$ and every input $u\in U_c$ with $u(0)=\xi$,
--   $$V(x)\ge\chi(\|\xi\|_U)\ \Longrightarrow\ \dot V_u(x)\le-\varphi(V(x)).$$
--
--   This is the continuous-time half of the small-gain theorem, quoted on p. 19 from [5, Theorem 5].
--
--   **Formalization Note** The page writes $\varphi(r)=\min_i(\sigma_i^{-1})'(\sigma_i(r))\,\varphi_i(\sigma_i(r))$ (4.12); since $\sigma_i^{-1}$ is only locally Lipschitz and differentiable almost everywhere, the statement asserts the existence of some positive definite $\varphi$. The page also claims the implication at $x=0$; that claim fails when some $\sigma_i^{-1}$ is not Lipschitz at $0$ (with $n=1$, $\dot x=-x+u$, $V_1=|x|$, $\sigma_1(r)=r^2$, $x=0$, $\xi=0$ and $u(t)=\min(t,1)$, one gets $\dot V_u(0)=1/\sqrt2>0$), so the statement is made for $x\ne0$. Hypothesis (4.5) is taken along the components of the interconnection's own flow; the Lie derivative is the Dini derivative in `EReal`.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 19, proof of Theorem 8, display before (4.12) and (4.12)

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.SmallGain

/-- The continuous part of the proof of Theorem 8 (arXiv:1212.5481v1, p. 19, display (4.12),
quoted from [5, Theorem 5]): under the hypotheses of Theorem 8 there is `φ ∈ 𝒫` such that for every
`x ≠ 0`, `ξ ∈ U` and input `u ∈ U_c` with `u(0) = ξ`, `V(x) ≥ χ(‖ξ‖)` implies
`V̇_u(x) ≤ −φ(V(x))`, where `V` is (4.10) and `χ` is (4.11). The page's
`φ(r) = minᵢ (σᵢ⁻¹)'(σᵢ(r)) φᵢ(σᵢ(r))` is replaced by an existential, because `σᵢ⁻¹` is
differentiable only almost everywhere. -/
theorem flow_decrease_4_12 {n : ℕ} {Xi : Fin n → Type*} [∀ i, NormedAddCommGroup (Xi i)]
    [∀ i, NormedSpace ℝ (Xi i)] [∀ i, CompleteSpace (Xi i)]
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveSystem ((i : Fin n) → Xi i) U) (hS : IsImpulsiveSystem S)
    (V : (i : Fin n) → Xi i → ℝ≥0) (ψ₁ ψ₂ : Fin n → ℝ≥0 → ℝ≥0)
    (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0) (χu : Fin n → ℝ≥0 → ℝ≥0) (φ α : Fin n → ℝ≥0 → ℝ≥0)
    (hV : IsSubsystemISSLyapunov S V ψ₁ ψ₂ χ χu φ α)
    (hSGC : SmallGainCondition (gainOp χ))
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (hσ : IsOmegaPath (gainOp χ) σ τ) :
    ∃ φ' : ℝ≥0 → ℝ≥0, IsPosDef φ' ∧
      ∀ (x : (i : Fin n) → Xi i) (ξ : U) (u : ℝ → U), x ≠ 0 → IsPCInput u → u 0 = ξ →
        smallGainChi τ χu ‖ξ‖₊ ≤ smallGainV τ V x →
        lieDeriv S (smallGainV τ V) x u ≤ ((-(φ' (smallGainV τ V x)) : ℝ) : EReal) := by sorry

end ImpulsiveISS.SmallGain
