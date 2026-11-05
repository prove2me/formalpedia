-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_theorem_3_2
-- name    : MagnonCode.AQEDC.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:20.080571+00:00
-- url     : https://prove2.me/theorems/1f37cefe-7c8a-420c-a168-10dd4ed5c456
-- title:
--   Theorem 3.2: approximate Knill-Laflamme conditions imply approximate error-detection
-- statement:
--   Let $\mathcal N(\rho)=\sum_{j\in[J]}R_j\rho R_j^\dagger$ be a CPTP map on $\mathcal B((\mathbb C^p)^{\otimes n})$, and let $\mathcal C$ be a subspace with orthonormal basis $\{\psi_\alpha\}_{\alpha\in[K]}$. Let $\epsilon_{\mathrm{approx}}$ be defined by
--
--   $$
--   \epsilon_{\mathrm{approx}}:=\max_{\alpha,\beta\in[K]}\sum_{j\in[J]}\bigl|\langle\psi_\alpha|R_j|\psi_\beta\rangle-\delta_{\alpha,\beta}\langle\psi_1|R_j|\psi_1\rangle\bigr|^2,
--   $$
--
--   and let $\delta>K^5\epsilon_{\mathrm{approx}}$. Then $\mathcal C$ is an $(\epsilon,\delta)$-approximate quantum error-detection code for $\mathcal N$ with $\epsilon=K^5\epsilon_{\mathrm{approx}}\delta^{-1}$.
--
--   This is the general sufficient condition behind Corollary 3.4.
--
--   Differences from the source:
--   - encoding: subspace C with orthonormal basis {ψ_α}_{α∈[K]} → projector P with range the span of ψ, orthonormal ψ indexed by a finite type with distinguished α₀ for the index 1; reason: Definition 3.1 gives the code with its projection; same instances
--   - encoding: (ε, δ)-approximate error-detection code (Definition 3.1) → IsDetecting, which also assumes t = tr(P N(|Ψ⟩⟨Ψ|)) ≠ 0 before concluding; reason: δ > 0 here and δ ≤ t, so t ≠ 0 always holds and the clause changes no instance; it only excludes the case where the printed ρ_{N,P} = t⁻¹ P N(|Ψ⟩⟨Ψ|) P is undefined
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Theorem 3.2, p. 11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_EastinKnill_Transversal_Setting
import Definitions.Def_MagnonCode_AQEDC_IsDetecting
import Definitions.Def_MagnonCode_AQEDC_epsApprox

open scoped Matrix

namespace MagnonCode.AQEDC

/-- **Theorem 3.2** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 11): let `N(ρ) = Σ_j R_j ρ R_j†` be CPTP on `B((ℂ^p)^{⊗n})`, let the code
have orthonormal basis `{ψ_α}_{α ∈ [K]}`, and let `δ > K⁵ ε_approx`, with `ε_approx` from (3). Then the
code is an `(ε, δ)`-approximate error-detection code for `N` with `ε = K⁵ ε_approx δ⁻¹`.

**Formalization Note** The code is the range of the projector `P`, spanned by `ψ`. CPTP is
`IsKrausFamily R`; `δ > 0` follows from `ε_approx ≥ 0`. -/
theorem theorem_3_2 {p n : ℕ} {K J : Type*} [Fintype K] [DecidableEq K] [Fintype J] (α₀ : K)
    (R : J → Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ) (hR : QAlgorithms.IsKrausFamily R)
    (P : Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ)
    (hP : EastinKnill.Transversal.IsCodeProjector P)
    (ψ : K → (Fin n → Fin p) → ℂ)
    (hψ : ∀ α β, star (ψ α) ⬝ᵥ ψ β = if α = β then 1 else 0)
    (hspan : LinearMap.range P.mulVecLin = Submodule.span ℂ (Set.range ψ))
    (δ : ℝ) (hδ : (Fintype.card K : ℝ) ^ 5 * epsApprox α₀ R ψ < δ) :
    IsDetecting ((Fintype.card K : ℝ) ^ 5 * epsApprox α₀ R ψ * δ⁻¹) δ P
      (QAlgorithms.krausApply R) := by sorry

end MagnonCode.AQEDC
