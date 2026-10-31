-- Prove2me | Theorems.Thm_MaskedLinx_proposition_3_1_diagonal_optimal_scaling
-- name    : MaskedLinx.proposition_3_1_diagonal_optimal_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:03.247007+00:00
-- url     : https://prove2.me/theorems/1494deaa-e55e-44c4-9c2f-6ee5d367c92a
-- title:
--   Proposition 3.1 — $\hat\gamma=1/d_s^2$ is an optimal scaling parameter for diagonal positive definite $C$
-- statement:
--   Let $C=\mathrm{Diag}(d_1,\dots,d_n)$ be a diagonal positive definite matrix with $d_1\ge\dots\ge d_n>0$, and let $0<s<n$. Put $\hat\gamma=1/d_s^2$. Then:
--
--   1. the scaled linx relaxation (2) at $\gamma=\hat\gamma$ has an optimal solution in $\{0,1\}^n$;
--   2. therefore $\hat\gamma$ is an optimal scaling parameter:
--
--   $$\mathrm{linx}(C,s;\hat\gamma)=\min_{\gamma>0}\mathrm{linx}(C,s;\gamma),$$
--
--   i.e. $\mathrm{linx}(C,s;\hat\gamma)\le\mathrm{linx}(C,s;\gamma)$ for every $\gamma>0$.
--
--   For the identity matrix ($d=e$) this gives $\hat\gamma=1$ and the optimal value $0$. This is how the paper evaluates the identity-masked bound in Theorem 4.1.
--
--   **Formalization Note** Indices are `Fin n` (0-based), so the paper's $d_s$ (the $s$-th largest entry) is `d ⟨s - 1, _⟩`, and $d_1\ge\dots\ge d_n$ is `Antitone d`.
--
--   Differences from the source:
--   - reading: "γ̂ forces an optimal solution of (2) to lie in {0,1}ⁿ" → some optimal solution of (2) at γ̂ lies in {0,1}ⁿ; reason: the universal reading is false when d_s = d_{s+1} (e.g. d = e, s = 1, n = 2: every x ∈ P(2,1) is optimal at γ̂ = 1); the paper's proof exhibits one binary optimal solution
--   - encoding: linx(C,s;γ̂) = min_{γ>0} linx(C,s;γ) → ∀ γ > 0, linx C s γ̂ ≤ linx C s γ, linx an EReal supremum; reason: γ̂ > 0 is in the range, so this says γ̂ attains the minimum
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Proposition 3.1, p.8

import Mathlib
import Definitions.Def_MaskedLinx_linx
import Definitions.Def_MaskedLinx_IsOptimalSolution

namespace MaskedLinx

/-- **Proposition 3.1 (optimal scaling `γ̂ = 1/d_s²` for diagonal positive-definite `C`).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Proposition 3.1, p.8:
"For diagonal positive-definite matrix C := Diag{d₁,...,dₙ}, where d₁ ≥ ... ≥ dₙ > 0 and
0 < s < n, the scaling parameter γ̂ = 1/d_s² forces an optimal solution of (2) to lie in
{0,1}ⁿ. Therefore γ̂ is an optimal scaling parameter."

Two clauses: (a) some optimal solution of (2) at `γ = γ̂` lies in `{0,1}ⁿ`; (b) `γ̂` is an
optimal scaling parameter: `linx(C,s;γ̂) ≤ linx(C,s;γ)` for every `γ > 0`.

**Formalization Note.** Indices are `Fin n` (0-based), so the paper's `d_s` (the `s`-th largest
entry, 1-based) is `d ⟨s - 1, _⟩`; `d₁ ≥ ⋯ ≥ dₙ` is `Antitone d`. "An optimal solution" is read
existentially: when `d_s = d_{s+1}` non-binary optimal solutions also exist at `γ̂`. -/
theorem proposition_3_1_diagonal_optimal_scaling (n : ℕ) (d : Fin n → ℝ) (hd : Antitone d)
    (hpos : ∀ i, 0 < d i) (s : ℕ) (hs0 : 0 < s) (hsn : s < n) :
    (∃ xhat : Fin n → ℝ, (∀ i, xhat i = 0 ∨ xhat i = 1) ∧
      IsOptimalSolution (Matrix.diagonal d) s (1 / d ⟨s - 1, by omega⟩ ^ 2) xhat) ∧
    ∀ γ : ℝ, 0 < γ →
      linx (Matrix.diagonal d) s (1 / d ⟨s - 1, by omega⟩ ^ 2) ≤ linx (Matrix.diagonal d) s γ := by sorry

end MaskedLinx
