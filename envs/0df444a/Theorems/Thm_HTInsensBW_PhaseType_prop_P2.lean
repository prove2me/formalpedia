-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_prop_P2
-- name    : HTInsensBW.PhaseType.prop_P2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:23.602715+00:00
-- url     : https://prove2.me/theorems/908c25c2-2743-47fc-9575-85a8e64bc2bf
-- title:
--   (P2'), p. 26 — ⟨b^(ℓ) − b̂^(ℓ), (−S^T)(ρ^(0) − nx)⟩ ≥ κ_min η_min ‖b^(ℓ) − b̂^(ℓ)‖²
-- statement:
--   Let $H$ have $0/1$ entries, let the weights $\kappa_r$ and base arrival rates $\lambda^{(0)}_r$ be positive, and let $x$ be any allocation rule. There is a constant $\eta_{\min}>0$ such that for every state $\mathbf n$ and every link $\ell$,
--   $$\big\langle\mathbf b^{(\ell)}-\widehat{\mathbf b}^{(\ell)},(-S^T)(\boldsymbol\rho^{(0)}-\mathbf n\mathbf x)\big\rangle\ \ge\ \kappa_{\min}\,\eta_{\min}\,\big\|\mathbf b^{(\ell)}-\widehat{\mathbf b}^{(\ell)}\big\|^2 ,$$
--   where $\kappa_{\min}=\min_r\kappa_r$, $\widehat b^{(\ell)}_{r,k}=n_{r,k}x_r\mathbb 1_{\{\ell\in r\}}/\kappa_r$, and the inner product and norm are those of (65).
--
--   Under the Euclidean inner product the left side would equal the squared distance itself; (P2') says that the rotation by $-S^T$ does not destroy this positivity under the constructed inner product.
--
--   **Formalization Note** The paper's $\eta_{\min}$ is "a positive constant to be defined later" (p. 27), so it is existential here, chosen before $\mathbf n$ and $\ell$.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 26–27, property (P2')

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Property (P2'), p. 26.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 26–27, (P2').)
There is a constant `η_min > 0` such that for every state `n` and every link `ℓ`,
`⟨b^(ℓ) - b̂^(ℓ), (-Sᵀ)(ρ^(0) - nx)⟩ ≥ κ_min η_min ‖b^(ℓ) - b̂^(ℓ)‖²`, with `κ_min = min_r κ_r`.

**Formalization Note** `η_min` is "a positive constant to be defined later" (p. 27), hence
existential, chosen before `n` and `ℓ`. `x` is arbitrary (no optimality is used). Hypotheses:
0/1 routing matrix, `κ_r > 0`, `λ^(0)_r > 0` (standing). -/
theorem prop_P2 {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) (x : (Fin R → ℕ) → Fin R → ℝ) :
    ∃ ηmin : ℝ, 0 < ηmin ∧ ∀ (n : State N) (ℓ : Fin L),
      kappaMin N * ηmin * msq N (bvec N ℓ - bhat N x n ℓ) ≤
        mInner N (bvec N ℓ - bhat N x n ℓ) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) := by sorry

end HTInsensBW.PhaseType
