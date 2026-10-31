-- Prove2me | Theorems.Thm_MaskedLinx_corollary_3_7_finite_optimal_scaling
-- name    : MaskedLinx.corollary_3_7_finite_optimal_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:04.497813+00:00
-- url     : https://prove2.me/theorems/bd045205-8146-4c19-b4fa-a3fa657a1950
-- title:
--   Corollary 3.7 — a finite optimal scaling parameter exists when $s<\mathrm{rank}(C)$
-- statement:
--   Let $C$ be a positive semidefinite real matrix of order $n$ and let $0<s<n$ with $s<\mathrm{rank}(C)$. Then there is a finite optimal scaling parameter $\hat\gamma>0$:
--
--   $$\mathrm{linx}(C,s;\hat\gamma)=\min_{\gamma>0}\mathrm{linx}(C,s;\gamma),$$
--
--   that is, $\mathrm{linx}(C,s;\hat\gamma)\le\mathrm{linx}(C,s;\gamma)$ for every $\gamma>0$.
--
--   In Theorem 4.1 this is what makes the minimum of the unmasked scaled bound over $\gamma$ attained.
--
--   **Formalization Note** $\mathrm{rank}(C)$ is `Matrix.rank C` over $\mathbb R$; indices are `Fin n`.
--
--   Differences from the source:
--   - encoding: a finite γ̂ with linx(C,s;γ̂) = min_{γ>0} linx(C,s;γ) → ∃ γ̂ : ℝ, 0 < γ̂ ∧ ∀ γ > 0, linx C s γ̂ ≤ linx C s γ, linx an EReal supremum; reason: a real γ̂ > 0 attaining the minimum is exactly a finite optimal scaling parameter
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Corollary 3.7, p.10

import Mathlib
import Definitions.Def_MaskedLinx_linx

namespace MaskedLinx

/-- **Corollary 3.7 (a finite optimal scaling parameter exists when `s < rank C`).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Corollary 3.7, p.10:
"For all positive-semidefinite C and 0 < s < n where s < rank(C), we can find a finite optimal
scaling parameter γ̂ such that linx(C,s;γ̂) = min_{γ>0} linx(C,s;γ)."

"Finite optimal scaling parameter" is a real `γ̂ > 0` with `linx(C,s;γ̂) ≤ linx(C,s;γ)` for every
`γ > 0`.

**Formalization Note.** `rank(C)` is `Matrix.rank C` over `ℝ`; indices are `Fin n`. -/
theorem corollary_3_7_finite_optimal_scaling (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) (s : ℕ) (hs0 : 0 < s) (hsn : s < n) (hrank : s < C.rank) :
    ∃ γhat : ℝ, 0 < γhat ∧ ∀ γ : ℝ, 0 < γ → linx C s γhat ≤ linx C s γ := by sorry

end MaskedLinx
