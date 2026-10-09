-- Prove2me | Theorems.Thm_ImpulsiveISS_SmallGain_alphaTilde_posDef
-- name    : ImpulsiveISS.SmallGain.alphaTilde_posDef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:01:56.516932+00:00
-- url     : https://prove2.me/theorems/b9c6833c-05d8-4c5b-8c26-d228c8729522
-- title:
--   Proof of Theorem 8, p. 20 — $\tilde\alpha=\max_i\sigma_i^{-1}\circ\alpha_i\circ\sigma_i$ is positive definite
-- statement:
--   Let $n\ge1$, let $\alpha_1,\dots,\alpha_n:\mathbb R_+\to\mathbb R_+$ be positive definite (continuous, with $\alpha_i(r)=0\iff r=0$), and let $\sigma=(\sigma_1,\dots,\sigma_n)$ be an $\Omega$-path (with respect to some operator $T$) with inverses $\sigma_i^{-1}$. Then
--   $$\tilde\alpha(r)=\max_{i=1}^n\ \sigma_i^{-1}\big(\alpha_i(\sigma_i(r))\big)$$
--   is positive definite.
--
--   In the proof of Theorem 8 this is the first step of the jump estimate: $\tilde\alpha$ collects the subsystems' jump rates in the coordinates of the $\Omega$-path.
--
--   **Formalization Note** The hypothesis $n\ge1$ is the paper's implicit standing assumption; for $n=0$ the maximum over the empty index set is $0$, which is not positive definite. Only the properties $\sigma_i\in\mathcal K_\infty$ and $\sigma_i^{-1}\circ\sigma_i=\sigma_i\circ\sigma_i^{-1}=\mathrm{id}$ of the $\Omega$-path are needed; the statement assumes the whole $\Omega$-path predicate of the referenced `Gains` definition.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 20, proof of Theorem 8, first sentence

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.SmallGain

/-- Proof of Theorem 8 (arXiv:1212.5481v1, p. 20): if every `αᵢ` is positive definite and `σ` is
an Ω-path (with `τᵢ = σᵢ⁻¹`), then `α̃ = maxᵢ σᵢ⁻¹ ∘ αᵢ ∘ σᵢ` is positive definite (`n ≥ 1`). -/
theorem alphaTilde_posDef {n : ℕ} (hn : 0 < n) (α : Fin n → ℝ≥0 → ℝ≥0)
    (hα : ∀ i, IsPosDef (α i))
    (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (hσ : IsOmegaPath T σ τ) :
    IsPosDef (alphaTilde σ τ α) := by sorry

end ImpulsiveISS.SmallGain
