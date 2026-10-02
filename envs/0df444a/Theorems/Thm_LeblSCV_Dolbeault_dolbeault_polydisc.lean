-- Prove2me | Theorems.Thm_LeblSCV_Dolbeault_dolbeault_polydisc
-- name    : LeblSCV.Dolbeault.dolbeault_polydisc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T20:48:30.975783+00:00
-- url     : https://prove2.me/theorems/e4525e40-6ba0-4002-9fc7-91185a8a073a
-- title:
--   Theorem 4.4.5 — H^(p,q)(Δ) = 0 for q ≥ 1 on possibly unbounded polydiscs
-- statement:
--   Let $\Delta\subset\mathbb{C}^n$ be a possibly unbounded polydisc (a product of discs and copies of $\mathbb{C}$), let $p\ge0$ and $q\ge1$ be integers, and let $\eta$ be a smooth $(p,q)$-form on $\Delta$ with $\bar\partial\eta = 0$. Then there is a smooth $(p,q-1)$-form $\omega$ on $\Delta$ with
--   $$\bar\partial\omega = \eta \quad\text{on } \Delta .$$
--   In other words, $H^{(p,q)}(\Delta) = 0$ for $q \ge 1$. The $\bar\partial$-problem is globally solvable on polydiscs, including $\mathbb{C}^n$; this is the input for the Cousin I problem (Theorem 4.6.5).
--
--   **Formalization Note.** Forms are coefficient families (`FormCoeffs`), smooth of bidegree $(p,q)$ in the sense of `IsSmoothForm` (all coefficients `ContDiffOn ℝ ∞` on $\Delta$, off-bidegree coefficients zero on $\Delta$), $\bar\partial$ is `dbar` of Definition 4.4.1, and $\omega$ is required to be smooth (Definition 4.4.1 makes every form smooth). The conclusion is stated directly; it is `DolbeaultVanishes Δ p q` for $q\ge1$. $q-1$ is natural-number subtraction, guarded by $q \ge 1$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 141, Theorem 4.4.5

import Mathlib
import Definitions.Def_LeblSCV_Dolbeault_IsPossiblyUnboundedPolydisc
import Definitions.Def_LeblSCV_Dolbeault_DolbeaultVanishes

namespace LeblSCV.Dolbeault

/-- Theorem 4.4.5 (Lebl, p. 141). Let `Δ ⊆ ℂⁿ` be a possibly unbounded polydisc, `p ≥ 0` and `q ≥ 1`,
and let `η` be a smooth `(p, q)`-form on `Δ` with `∂̄η = 0`. Then there is a smooth `(p, q - 1)`-form
`ω` on `Δ` with `∂̄ω = η` on `Δ`. In other words `H^{(p,q)}(Δ) = 0` for `q ≥ 1`. -/
theorem dolbeault_polydisc {n : ℕ} (Δ : Set (Fin n → ℂ)) (hΔ : IsPossiblyUnboundedPolydisc Δ)
    (p q : ℕ) (hq : 1 ≤ q) (η : FormCoeffs n) (hη : IsSmoothForm Δ p q η)
    (hclosed : IsDbarClosed Δ η) :
    ∃ ω : FormCoeffs n, IsSmoothForm Δ p (q - 1) ω ∧
      ∀ A B : Finset (Fin n), ∀ z ∈ Δ, dbar ω A B z = η A B z := by sorry

end LeblSCV.Dolbeault
