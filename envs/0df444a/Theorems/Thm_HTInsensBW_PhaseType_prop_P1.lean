-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_prop_P1
-- name    : HTInsensBW.PhaseType.prop_P1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:21.636575+00:00
-- url     : https://prove2.me/theorems/d0ea0bf6-1c96-40ac-a08b-3699aa55f7db
-- title:
--   (P1'), p. 26 — ⟨b^(ℓ), (−S^T)(ρ^(0) − nx)⟩ = U_ℓ − δ_ℓ
-- statement:
--   Let the weights $\kappa_r$ and base arrival rates $\lambda^{(0)}_r$ be positive, let $x$ be any allocation rule (a function of the route counts), and use the inner product $\langle\cdot,\cdot\rangle$ of (65). For every state $\mathbf n$ and every link $\ell$,
--   $$\big\langle\mathbf b^{(\ell)},(-S^T)(\boldsymbol\rho^{(0)}-\mathbf n\mathbf x)\big\rangle=U_\ell-\delta_\ell ,$$
--   where $U_\ell=C_\ell-\sum_{r:\ell\in r}n_rx_r$ is the unused bandwidth and $\delta_\ell=C_\ell-\sum_{r:\ell\in r}\rho^{(0)}_r$ the capacity surplus of link $\ell$.
--
--   Property (P1') says that, measured along $\mathbf b^{(\ell)}$, the difference between the loads and the current allocation is exactly the idle capacity of link $\ell$ beyond its surplus; it is the phase-type replacement of (P1).
--
--   **Formalization Note** The identity does not use optimality of the allocation, so $x$ is arbitrary.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 26, property (P1')

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Property (P1'), p. 26.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 26, (P1').)
For every state `n` and every link `ℓ`, `⟨b^(ℓ), (-Sᵀ)(ρ^(0) - nx)⟩ = U_ℓ - δ_ℓ`, where `U_ℓ` is the
unused bandwidth and `δ_ℓ` the capacity surplus of link `ℓ`.

**Formalization Note** The identity uses no optimality of the allocation, so `x` is an arbitrary
function of the route totals. Hypotheses `κ_r > 0`, `λ^(0)_r > 0` (standing). -/
theorem prop_P1 {L R : ℕ} (N : BWNetwork L R)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) (x : (Fin R → ℕ) → Fin R → ℝ) :
    ∀ (n : State N) (ℓ : Fin L),
      mInner N (bvec N ℓ) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) = unused N x n ℓ - slack N ℓ := by sorry

end HTInsensBW.PhaseType
