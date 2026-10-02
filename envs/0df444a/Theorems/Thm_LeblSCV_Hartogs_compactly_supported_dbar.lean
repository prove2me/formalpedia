-- Prove2me | Theorems.Thm_LeblSCV_Hartogs_compactly_supported_dbar
-- name    : LeblSCV.Hartogs.compactly_supported_dbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:57:46.965617+00:00
-- url     : https://prove2.me/theorems/7f655bb9-2bcb-49cc-bf58-888ae464867d
-- title:
--   Theorem 4.2.1 — the compactly supported ∂̄-problem in ℂⁿ, n ≥ 2
-- statement:
--   Let $n \ge 2$ and let $g = g_1\, d\bar z_1 + \cdots + g_n\, d\bar z_n$ be a $(0,1)$-form on $\mathbb{C}^n$ whose coefficients $g_j : \mathbb{C}^n \to \mathbb{C}$ are smooth and compactly supported, and which satisfies the compatibility conditions
--   $$\frac{\partial g_k}{\partial \bar z_\ell} = \frac{\partial g_\ell}{\partial \bar z_k} \qquad \text{for all } k, \ell = 1, \dots, n. \tag{4.1}$$
--   Then there exists a unique compactly supported smooth function $\psi : \mathbb{C}^n \to \mathbb{C}$ such that $\bar\partial\psi = g$, that is,
--   $$\frac{\partial \psi}{\partial \bar z_k} = g_k \qquad \text{for } k = 1, \dots, n.$$
--
--   The dimension hypothesis is essential: for $n = 1$ a solution exists but in general none has compact support. This theorem is the analytic input of the Hartogs phenomenon (Theorem 4.3.1).
--
--   **Formalization Note.** The form is represented by its coefficient tuple `g : Fin n → (Fin n → ℂ) → ℂ`; $\partial/\partial\bar z_k$ is `wirtingerBar k`. Smooth is real $C^\infty$ (`ContDiff ℝ ∞`), compact support is `HasCompactSupport`. Uniqueness is uniqueness among compactly supported smooth functions, stated with `∃!`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 132, Theorem 4.2.1

import Mathlib
import Definitions.Def_LeblSCV_Shared_wirtingerBar

open scoped ContDiff

namespace LeblSCV.Hartogs

/-- Theorem 4.2.1 (Lebl, p. 132). Let `n ≥ 2` and let `g = g_1 dz̄_1 + ⋯ + g_n dz̄_n` be a
`(0,1)`-form on `ℂⁿ` whose coefficients `g_j : ℂⁿ → ℂ` are compactly supported smooth functions
satisfying the compatibility conditions (4.1) `∂g_k/∂z̄_ℓ = ∂g_ℓ/∂z̄_k` for all `k, ℓ`. Then there is
a unique compactly supported smooth `ψ : ℂⁿ → ℂ` with `∂̄ψ = g`, i.e. `∂ψ/∂z̄_k = g_k` for every `k`.
The form is represented by its coefficient tuple `g : Fin n → (ℂⁿ → ℂ)`; smooth is real `C^∞`. -/
theorem compactly_supported_dbar {n : ℕ} (hn : 2 ≤ n) (g : Fin n → (Fin n → ℂ) → ℂ)
    (hg_smooth : ∀ j, ContDiff ℝ ∞ (g j))
    (hg_supp : ∀ j, HasCompactSupport (g j))
    (hcompat : ∀ k l : Fin n, LeblSCV.Shared.wirtingerBar l (g k) = LeblSCV.Shared.wirtingerBar k (g l)) :
    ∃! ψ : (Fin n → ℂ) → ℂ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ ∀ k : Fin n, LeblSCV.Shared.wirtingerBar k ψ = g k := by sorry

end LeblSCV.Hartogs
