-- Prove2me | Theorems.Thm_MaskedLinx_proposition_1_1_binary_optimal_scaling
-- name    : MaskedLinx.proposition_1_1_binary_optimal_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:20.447874+00:00
-- url     : https://prove2.me/theorems/4bf802a8-fbf8-4227-9c6d-f00574c4a55f
-- title:
--   Proposition 1.1 — a binary optimal solution at $\hat\gamma$ makes $\hat\gamma$ an optimal scaling parameter
-- statement:
--   Let $C$ be a positive semidefinite real matrix of order $n$ (a covariance matrix), let $s$ be a natural number and let $\hat\gamma>0$. If some $\hat x\in\{0,1\}^n$ is an optimal solution of the scaled linx relaxation (2) at $\gamma=\hat\gamma$, then $\hat\gamma$ is an optimal scaling parameter:
--
--   $$\mathrm{linx}(C,s;\hat\gamma)=\min_{\gamma>0}\mathrm{linx}(C,s;\gamma),$$
--
--   that is, $\mathrm{linx}(C,s;\hat\gamma)\le\mathrm{linx}(C,s;\gamma)$ for every $\gamma>0$.
--
--   The reason is that the relaxation is exact: at a $0/1$ point the scaled objective equals $\mathrm{ldet}\,C[S,S]$ for $S$ the support, whatever $\gamma$ is. The proposition is the paper's route to optimal scaling parameters in closed form.
--
--   **Formalization Note** Positive semidefiniteness of $C$ is the paper's standing assumption (§1: $C$ is a covariance matrix). Indices are `Fin n`.
--
--   Differences from the source:
--   - encoding: linx(C,s;γ̂) = min_{γ>0} linx(C,s;γ) → ∀ γ > 0, linx C s γ̂ ≤ linx C s γ, with linx an EReal supremum (ldet = ⊥ off the positive definite matrices); reason: γ̂ > 0 is itself in the range, so this is the statement that γ̂ attains the minimum
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Proposition 1.1, p.2 (standing assumption on C, §1, p.1)

import Mathlib
import Definitions.Def_MaskedLinx_linx
import Definitions.Def_MaskedLinx_IsOptimalSolution

namespace MaskedLinx

/-- **Proposition 1.1 (a binary optimal solution certifies an optimal scaling).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Proposition 1.1, p.2:
"If x̂ ∈ {0,1}ⁿ is an optimal solution of (2) for γ = γ̂, then γ̂ is optimal.
That is, linx(C,s;γ̂) = min_{γ>0} linx(C,s;γ)."

The conclusion "`= min_{γ>0}`" is stated as: `linx(C,s;γ̂) ≤ linx(C,s;γ)` for every `γ > 0`
(and `γ̂ > 0` is itself in the range).

**Formalization Note.** `C` is positive semidefinite: the paper's standing assumption (§1, p.1)
that `C` is a covariance matrix. Indices are `Fin n`. -/
theorem proposition_1_1_binary_optimal_scaling (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) (s : ℕ) (γhat : ℝ) (hγhat : 0 < γhat) (xhat : Fin n → ℝ)
    (hbin : ∀ i, xhat i = 0 ∨ xhat i = 1) (hopt : IsOptimalSolution C s γhat xhat) :
    ∀ γ : ℝ, 0 < γ → linx C s γhat ≤ linx C s γ := by sorry

end MaskedLinx
