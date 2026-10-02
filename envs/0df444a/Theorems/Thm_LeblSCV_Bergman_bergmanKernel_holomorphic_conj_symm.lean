-- Prove2me | Theorems.Thm_LeblSCV_Bergman_bergmanKernel_holomorphic_conj_symm
-- name    : LeblSCV.Bergman.bergmanKernel_holomorphic_conj_symm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:32.164701+00:00
-- url     : https://prove2.me/theorems/aa11c71a-38ed-483f-a09f-0c84a0889c27
-- title:
--   Proposition 5.2.2 — the Bergman kernel is holomorphic in $z$, antiholomorphic in $\zeta$, and conjugate symmetric
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain with Bergman kernel $K_U(z, \bar\zeta)$, $z, \zeta \in U$. Then $K_U(z, \bar\zeta)$ is holomorphic in $z$ (for each fixed $\zeta \in U$), antiholomorphic in $\zeta$ (for each fixed $z \in U$, $\zeta \mapsto \overline{K_U(z, \bar\zeta)}$ is holomorphic on $U$), and
--   $$\overline{K_U(z, \bar\zeta)} = K_U(\zeta, \bar z) \qquad (z, \zeta \in U).$$
--
--   Thinking of $\bar\zeta$ as the variable, $K_U$ is thus a holomorphic function of each of its $n$-tuples of variables, and conjugate symmetric; this is used in the proof of Proposition 5.2.5.
--
--   **Formalization Note.** `bergmanKernel U z ζ` is $K_U(z, \bar\zeta)$, so $K_U(\zeta, \bar z)$ is `bergmanKernel U ζ z`. Holomorphic is `DifferentiableOn ℂ` on the open set $U$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 162, Proposition 5.2.2

import Mathlib
import Definitions.Def_LeblSCV_Bergman_bergmanKernel

open MeasureTheory

namespace LeblSCV.Bergman

/-- Lebl, Proposition 5.2.2 (p. 162). For a domain `U ⊆ ℂⁿ`, the Bergman kernel `K_U(z, ζ̄)` is
holomorphic in `z`, antiholomorphic in `ζ`, and `\overline{K_U(z, ζ̄)} = K_U(ζ, z̄)`.
Here `bergmanKernel U z ζ` is `K_U(z, ζ̄)`, so "antiholomorphic in `ζ`" means that
`ζ ↦ \overline{K_U(z, ζ̄)}` is holomorphic on `U`. -/
theorem bergmanKernel_holomorphic_conj_symm {n : ℕ} {U : Set (Fin n → ℂ)} (hU_open : IsOpen U)
    (hU_conn : IsConnected U) :
    (∀ ζ ∈ U, DifferentiableOn ℂ (fun z => bergmanKernel U z ζ) U) ∧
      (∀ z ∈ U, DifferentiableOn ℂ (fun ζ => (starRingEnd ℂ) (bergmanKernel U z ζ)) U) ∧
      (∀ z ∈ U, ∀ ζ ∈ U, (starRingEnd ℂ) (bergmanKernel U z ζ) = bergmanKernel U ζ z) := by sorry

end LeblSCV.Bergman
