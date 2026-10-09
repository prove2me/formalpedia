-- Prove2me | Theorems.Thm_ImpulsiveISS_SmallGain_jump_estimate
-- name    : ImpulsiveISS.SmallGain.jump_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:29.066188+00:00
-- url     : https://prove2.me/theorems/8c9077de-4113-4c34-907a-3521432a3f52
-- title:
--   Proof of Theorem 8, pp. 19–20 — jump estimate $V(g(x,\xi))\le\max\{\alpha^*(V(x)),\eta(V(x)),\chi(\|\xi\|)\}$ for every $\alpha^*\in\mathcal K$ with $\alpha^*\ge\tilde\alpha$
-- statement:
--   Consider an interconnection of $n$ impulsive subsystems on $X=X_1\times\dots\times X_n$ with jump map $g=(g_1,\dots,g_n)$, and let $V_i$ be ISS-Lyapunov functions for the subsystems with gains $\chi_{ij}$, $\chi_i$ and jump rates $\alpha_i$ as in (4.4)–(4.6). Let $\sigma$ be an $\Omega$-path for the gain operator $\Gamma$ of (4.7), with inverses $\sigma_i^{-1}$, and put
--   $$V(x)=\max_i\sigma_i^{-1}(V_i(x_i)),\quad \chi(r)=\max_i\sigma_i^{-1}(\chi_i(r)),\quad \tilde\alpha=\max_i\sigma_i^{-1}\circ\alpha_i\circ\sigma_i,\quad \eta=\max_{i,j\ne i}\sigma_i^{-1}\circ\chi_{ij}\circ\sigma_j.$$
--
--   Then for every $\alpha^*\in\mathcal K$ with $\alpha^*(r)\ge\tilde\alpha(r)$ for all $r\ge0$, and all $x\in X$, $\xi\in U$,
--   $$V(g(x,\xi))\le\max\big\{\alpha^*(V(x)),\ \eta(V(x)),\ \chi(\|\xi\|_U)\big\}.$$
--
--   This is the discrete half of the small-gain theorem: with $\alpha=\max\{\alpha^*,\eta\}$ (4.13) it gives the max-form jump bound (3.6) for $V$.
--
--   **Formalization Note** The page passes through the bound $\alpha^*(V(x))$ with a monotone $\alpha^*\ge\tilde\alpha$; the bound with $\tilde\alpha(V(x))$ itself would be false in general, since $\tilde\alpha$ need not be increasing. The small-gain condition is not needed for this step and is not assumed.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, pp. 19–20, proof of Theorem 8, estimates of V(g(x, ξ)) from (4.6) through 'We continue estimates of V(g(x, ξ))'

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.SmallGain

/-- The jump estimate in the proof of Theorem 8 (arXiv:1212.5481v1, pp. 19–20): under the subsystem
hypotheses (items 1–3, p. 18) and an Ω-path `σ` for `Γ` (with `τᵢ = σᵢ⁻¹`), for every `α* ∈ 𝒦`
with `α* ≥ α̃` and all `x ∈ X`, `ξ ∈ U`,
`V(g(x, ξ)) ≤ max{α*(V(x)), η(V(x)), χ(‖ξ‖)}`, where `V` is (4.10) and `χ` is (4.11). -/
theorem jump_estimate {n : ℕ} {Xi : Fin n → Type*} [∀ i, NormedAddCommGroup (Xi i)]
    [∀ i, NormedSpace ℝ (Xi i)] [∀ i, CompleteSpace (Xi i)]
    {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : ImpulsiveSystem ((i : Fin n) → Xi i) U)
    (V : (i : Fin n) → Xi i → ℝ≥0) (ψ₁ ψ₂ : Fin n → ℝ≥0 → ℝ≥0)
    (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0) (χu : Fin n → ℝ≥0 → ℝ≥0) (φ α : Fin n → ℝ≥0 → ℝ≥0)
    (hV : IsSubsystemISSLyapunov S V ψ₁ ψ₂ χ χu φ α)
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (hσ : IsOmegaPath (gainOp χ) σ τ)
    (αstar : ℝ≥0 → ℝ≥0) (hαstar : IsK αstar) (hαstar_ge : ∀ r, alphaTilde σ τ α r ≤ αstar r) :
    ∀ (x : (i : Fin n) → Xi i) (ξ : U),
      smallGainV τ V (S.jump x ξ) ≤
        max (αstar (smallGainV τ V x)) (max (etaGain σ τ χ (smallGainV τ V x)) (smallGainChi τ χu ‖ξ‖₊)) := by sorry

end ImpulsiveISS.SmallGain
