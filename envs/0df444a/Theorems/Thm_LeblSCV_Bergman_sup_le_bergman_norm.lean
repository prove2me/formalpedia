-- Prove2me | Theorems.Thm_LeblSCV_Bergman_sup_le_bergman_norm
-- name    : LeblSCV.Bergman.sup_le_bergman_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:04:25.37686+00:00
-- url     : https://prove2.me/theorems/8cf5150b-8366-4cd4-8ba1-e39b2d8eea83
-- title:
--   Lemma 5.2.1 — the $A^2$ norm bounds the sup norm on compacts; $A^2(U)$ is complete
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain (a connected open set) and $K \subset U$ compact. Then there is a constant $C_K$ such that
--   $$\|f\|_K = \sup_{z \in K} |f(z)| \le C_K \, \|f\|_{A^2(U)} \qquad \text{for all } f \in A^2(U).$$
--   Consequently, $A^2(U)$ is complete, i.e. a Hilbert space.
--
--   The estimate says that point evaluation $f \mapsto f(z)$ is a bounded linear functional on $A^2(U)$, which is what makes the Bergman kernel exist (via the Riesz representation theorem); it also turns $L^2$ convergence in $A^2(U)$ into uniform convergence on compact sets.
--
--   **Formalization Note.** $f(z)$ is `holoRep U f z`, the value of the holomorphic representative. The constant is quantified after $U$ and $K$ and before $f$, so it may depend on $U$ and $K$ only. "$K \subset\subset U$ compact" is `IsCompact K ∧ K ⊆ U`; "domain" is `IsOpen U ∧ IsConnected U`. Completeness is `CompleteSpace (bergmanSpace U)`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 161, Lemma 5.2.1

import Mathlib
import Definitions.Def_LeblSCV_Bergman_holoRep

open MeasureTheory

namespace LeblSCV.Bergman

/-- Lebl, Lemma 5.2.1 (p. 161). Let `U ⊆ ℂⁿ` be a domain and `K ⊂⊂ U` compact. Then there is a
constant `C_K` with `‖f‖_K = sup_{z ∈ K} |f(z)| ≤ C_K ‖f‖_{A²(U)}` for all `f ∈ A²(U)`.
Consequently, `A²(U)` is complete. -/
theorem sup_le_bergman_norm {n : ℕ} {U : Set (Fin n → ℂ)} (hU_open : IsOpen U)
    (hU_conn : IsConnected U) {K : Set (Fin n → ℂ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    (∃ C : ℝ, ∀ f : bergmanSpace U, ∀ z ∈ K, ‖holoRep U f z‖ ≤ C * ‖f‖) ∧
      CompleteSpace (bergmanSpace U) := by sorry

end LeblSCV.Bergman
