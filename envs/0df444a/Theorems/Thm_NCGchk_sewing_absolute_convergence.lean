-- Prove2me | Theorems.Thm_NCGchk_sewing_absolute_convergence
-- name    : NCGchk.sewing_absolute_convergence
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T12:20:14.814806+00:00
-- url     : https://prove2.me/theorems/64816928-ea0b-5cb1-b88f-73e6766ab7d1
-- title:
--   Sewing absolute convergence (check)
-- statement:
--   Absolute convergence of the path-integral composition.

import Mathlib

namespace NCGchk
theorem sewing_absolute_convergence
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (e : ι → E) (he : Orthonormal ℂ e)
    (htotal : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤)
    (U₁ U₂ : E ≃ₗᵢ[ℂ] E) (φ ψ : E) :
    Summable (fun i : ι => ‖inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)‖) ∧
    (∑' i : ι, inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)) = inner ℂ φ (U₂ (U₁ ψ)) ∧
    (∑' i : ι, ‖inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)‖) ≤ ‖φ‖ * ‖ψ‖ := by sorry
end NCGchk
