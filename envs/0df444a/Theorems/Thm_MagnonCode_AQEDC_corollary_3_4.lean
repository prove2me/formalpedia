-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_corollary_3_4
-- name    : MagnonCode.AQEDC.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:24.647881+00:00
-- url     : https://prove2.me/theorems/6a2d5d1e-4e92-4457-906a-77b9660906f9
-- title:
--   Corollary 3.4: a sufficient condition for an $(\epsilon,\delta)[[n,k,d]]$-AQEDC
-- statement:
--   Let $K=p^k$ and let $\mathcal C\subset(\mathbb C^p)^{\otimes n}$ be a code with orthonormal basis $\{\psi_\alpha\}_{\alpha\in[K]}$ satisfying, for some $\gamma>0$,
--
--   $$
--   \bigl|\langle\psi_\alpha|F|\psi_\beta\rangle-\delta_{\alpha,\beta}\langle\psi_1|F|\psi_1\rangle\bigr|\le\gamma\|F\|\qquad\text{for all }\alpha,\beta\in[K],
--   $$
--
--   for every $d$-local operator $F$ on $(\mathbb C^p)^{\otimes n}$. Let $\delta>K^5\gamma^2$. Then $\mathcal C$ is an $(\epsilon,\delta)[[n,k,d]]$-AQEDC with $\epsilon=K^5\gamma^2\delta^{-1}$.
--
--   The condition involves only individual $d$-local operators, not whole channels.
--
--   Differences from the source:
--   - encoding: K = p^k, code with orthonormal basis {ψ_α}_{α∈[K]} → finite index type of cardinality K with (K : ℝ) = p^k and distinguished α₀, projector P with range the span of ψ; reason: k is real in the application; same instances
--   - encoding: (ε, δ)-approximate error-detection code (Definition 3.1) → IsDetecting, which also assumes t = tr(P N(|Ψ⟩⟨Ψ|)) ≠ 0 before concluding; reason: δ > 0 here and δ ≤ t, so t ≠ 0 always holds and the clause changes no instance; it only excludes the case where the printed ρ_{N,P} = t⁻¹ P N(|Ψ⟩⟨Ψ|) P is undefined
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Corollary 3.4, p. 12

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting
import Definitions.Def_MagnonCode_AQEDC_IsAQEDC

open scoped Matrix Matrix.Norms.L2Operator

namespace MagnonCode.AQEDC

/-- **Corollary 3.4** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 12): let `K = p^k`, let the code have orthonormal basis
`{ψ_α}_{α ∈ [K]}`, and let, for some `γ > 0`, `|⟨ψ_α|F|ψ_β⟩ − δ_{α,β}⟨ψ_1|F|ψ_1⟩| ≤ γ ‖F‖` for all
`α, β` (8) and every `d`-local `F`. Let `δ > K⁵γ²`. Then the code is an
`(K⁵γ²δ⁻¹, δ)[[n, k, d]]`-AQEDC.

**Formalization Note** `K` is the cardinality of a finite index type, nonempty through `α₀`, which plays
the printed index `1`. `‖·‖` is the L2 operator norm. -/
theorem corollary_3_4 {p n d : ℕ} {K : Type*} [Fintype K] [DecidableEq K] (α₀ : K) (k : ℝ)
    (hK : (Fintype.card K : ℝ) = (p : ℝ) ^ k)
    (P : Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ)
    (hP : EastinKnill.Transversal.IsCodeProjector P)
    (ψ : K → (Fin n → Fin p) → ℂ)
    (hψ : ∀ α β, star (ψ α) ⬝ᵥ ψ β = if α = β then 1 else 0)
    (hspan : LinearMap.range P.mulVecLin = Submodule.span ℂ (Set.range ψ))
    (γ : ℝ) (hγ : 0 < γ)
    (h8 : ∀ F : Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ, IsDLocal d F → ∀ α β,
      ‖star (ψ α) ⬝ᵥ F *ᵥ ψ β - (if α = β then star (ψ α₀) ⬝ᵥ F *ᵥ ψ α₀ else 0)‖ ≤ γ * ‖F‖)
    (δ : ℝ) (hδ : (Fintype.card K : ℝ) ^ 5 * γ ^ 2 < δ) :
    IsAQEDC p n k d ((Fintype.card K : ℝ) ^ 5 * γ ^ 2 * δ⁻¹) δ P := by sorry

end MagnonCode.AQEDC
