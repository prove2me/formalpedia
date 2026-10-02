-- Prove2me | Theorems.Thm_LeblSCV_Dolbeault_dolbeault_grothendieck
-- name    : LeblSCV.Dolbeault.dolbeault_grothendieck
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T20:24:57.180281+00:00
-- url     : https://prove2.me/theorems/2468b3fe-8268-4853-8d45-2c9ecc13812f
-- title:
--   Lemma 4.4.7 — Dolbeault–Grothendieck lemma
-- statement:
--   Let $\Delta_s(w) \subset \Delta_r(w) \subset \mathbb{C}^n$ be polydiscs with $0 < s_\ell < r_\ell < \infty$ for each $\ell$. Let $p \ge 0$ and $q\ge1$ be integers and let $\eta$ be a smooth $(p,q)$-form on $\Delta_r(w)$ with $\bar\partial\eta = 0$. Then there is a smooth $(p,q-1)$-form $\omega$ on $\Delta_s(w)$ with
--   $$\bar\partial\omega = \eta \quad\text{on } \Delta_s(w).$$
--   This is the $\bar\partial$-analogue of the Poincaré lemma: closed forms are exact on a slightly smaller polydisc.
--
--   **Formalization Note.** Forms are coefficient families (`FormCoeffs`), smooth of the given bidegree in the sense of `IsSmoothForm`; $\bar\partial$ is `dbar` (Definition 4.4.1). The polydiscs use the Euclidean modulus in each coordinate, as in Definition 1.1.1; $r_\ell<\infty$ is automatic for real radii. $q - 1$ is natural-number subtraction, guarded by $q\ge1$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 143, Lemma 4.4.7

import Mathlib
import Definitions.Def_LeblSCV_Shared_polydisc
import Definitions.Def_LeblSCV_Dolbeault_DolbeaultVanishes

namespace LeblSCV.Dolbeault

/-- Lemma 4.4.7 (Dolbeault–Grothendieck, Lebl, p. 143). Let `Δ_s(w) ⊆ Δ_r(w) ⊆ ℂⁿ` be polydiscs with
`0 < s_ℓ < r_ℓ < ∞` for each `ℓ`. Let `p ≥ 0` and `q ≥ 1`, and let `η` be a smooth `(p, q)`-form on
`Δ_r(w)` with `∂̄η = 0`. Then there is a smooth `(p, q - 1)`-form `ω` on `Δ_s(w)` with `∂̄ω = η` on
`Δ_s(w)`. -/
theorem dolbeault_grothendieck {n : ℕ} (w : Fin n → ℂ) (s r : Fin n → ℝ)
    (hs : ∀ l, 0 < s l) (hsr : ∀ l, s l < r l) (p q : ℕ) (hq : 1 ≤ q)
    (η : FormCoeffs n) (hη : IsSmoothForm (LeblSCV.Shared.polydisc w r) p q η)
    (hclosed : IsDbarClosed (LeblSCV.Shared.polydisc w r) η) :
    ∃ ω : FormCoeffs n, IsSmoothForm (LeblSCV.Shared.polydisc w s) p (q - 1) ω ∧
      ∀ A B : Finset (Fin n), ∀ z ∈ LeblSCV.Shared.polydisc w s, dbar ω A B z = η A B z := by sorry

end LeblSCV.Dolbeault
