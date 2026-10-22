-- Prove2me | Theorems.Thm_OgataLDP_FCS_equation_1
-- name    : OgataLDP.FCS.equation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:43.748571+00:00
-- url     : https://prove2.me/theorems/e5536a4f-a68b-431e-abe6-e445b6abe0bb
-- title:
--   Equation (1) — the spectral-law exponential moment equals the local-state exponential
-- statement:
--   Fix a finitely correlated state $\omega$, a translation-invariant finite-range interaction $\Phi$, an integer $n\ge1$, and $\alpha\in\mathbb R$. Let $\mu_{n,\Phi}$ be the spectral distribution of $H_\Phi([1,n])/n$ in the local state $\omega_n$. Then $\mu_{n,\Phi}$ is a probability measure and
--
--   $$\int_{\mathbb R} e^{n\alpha x}\,d\mu_{n,\Phi}(x)
--     =\omega_n\!\left(e^{\alpha H_\Phi([1,n])}\right).$$
--
--   This identity identifies the logarithmic moment generating function in Theorem 1.3 with the quantum state expression of equation (1).
--
--   **Formalization Note** The integral is a nonnegative lower integral. The real part of the state evaluation is taken because the matrix expectation is represented in $\mathbb C$; for this positive observable it is real.
-- source:
--   Ogata, arXiv:0803.0113v1, pp. 3–5, spectral distribution and equation (1) as used after Theorem 1.3

import Mathlib
import Definitions.Def_OgataLDP_FCS_Model

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open NormedSpace

namespace OgataLDP.FCS

/-- Ogata, arXiv:0803.0113v1, pp. 3–5, the spectral law and equation (1). -/
theorem equation_1 {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ] {k : ℕ}
    (F : FCSData σ k) (hF : F.IsValid) (Phi : Interaction σ)
    (n : ℕ) (hn : 0 < n) (a : ℝ) :
    IsProbabilityMeasure
      (specDist (F.localState n) (((n : ℝ)⁻¹ : ℝ) • Phi.hamiltonian n)) ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp ((n : ℝ) * a * x))
      ∂(specDist (F.localState n) (((n : ℝ)⁻¹ : ℝ) • Phi.hamiltonian n))) =
      ENNReal.ofReal ((F.localState n (exp ((a : ℂ) • Phi.hamiltonian n))).re) := by sorry

end OgataLDP.FCS
