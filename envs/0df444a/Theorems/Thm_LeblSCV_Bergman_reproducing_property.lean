-- Prove2me | Theorems.Thm_LeblSCV_Bergman_reproducing_property
-- name    : LeblSCV.Bergman.reproducing_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:06:04.405956+00:00
-- url     : https://prove2.me/theorems/31d59a6a-55f7-488e-bc1f-506d24206fbe
-- title:
--   Eq. (5.1) — reproducing property of the Bergman kernel
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain and $K_U$ its Bergman kernel. Then for every $f \in A^2(U)$ and every $z \in U$, the function $\zeta \mapsto f(\zeta) K_U(z, \bar\zeta)$ is integrable on $U$ and
--   $$f(z) = \int_U f(\zeta) \, K_U(z, \bar\zeta) \, dV(\zeta).$$
--
--   This is the reproducing property of the kernel. It amounts to the existence of the Riesz representer $k_z$ of evaluation at $z$ (Lemma 5.2.1 plus the Riesz representation theorem), and it is the identity through which Propositions 5.2.2 and 5.2.5 are proved.
--
--   **Formalization Note.** $K_U(z, \bar\zeta)$ is `bergmanKernel U z ζ` and $f(\zeta)$ is `holoRep U f ζ`. The integrability of the integrand is part of the conclusion, so the Bochner integral cannot be $0$ by default.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 162, Eq. (5.1)

import Mathlib
import Definitions.Def_LeblSCV_Bergman_bergmanKernel

open MeasureTheory

namespace LeblSCV.Bergman

/-- Lebl, Eq. (5.1) (p. 162), the reproducing property of the Bergman kernel: for a domain
`U ⊆ ℂⁿ`, every `f ∈ A²(U)` and every `z ∈ U`, `f(z) = ∫_U f(ζ) K_U(z, ζ̄) dV(ζ)`, the integrand
being integrable on `U`. Here `bergmanKernel U z ζ` is `K_U(z, ζ̄)`. -/
theorem reproducing_property {n : ℕ} {U : Set (Fin n → ℂ)} (hU_open : IsOpen U)
    (hU_conn : IsConnected U) (f : bergmanSpace U) {z : Fin n → ℂ} (hz : z ∈ U) :
    Integrable (fun ζ => holoRep U f ζ * bergmanKernel U z ζ) (volume.restrict U) ∧
      holoRep U f z = ∫ ζ in U, holoRep U f ζ * bergmanKernel U z ζ := by sorry

end LeblSCV.Bergman
