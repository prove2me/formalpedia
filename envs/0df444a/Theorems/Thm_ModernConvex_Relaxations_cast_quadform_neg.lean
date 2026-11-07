-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_cast_quadform_neg
-- name    : ModernConvex.Relaxations.cast_quadform_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:42.135426+00:00
-- url     : https://prove2.me/theorems/70ba3ba9-5676-4bcc-851a-7b107e9a046d
-- title:
--   A rational negative direction casts to a real negative direction
-- statement:
--   **A rational certificate transports to the reals.**
--
--   Let $M$ be a rational matrix and $v$ a rational vector with $v^{\mathsf T}Mv<0$. Then the cast vector $\tilde v=(\uparrow v_i)$ satisfies $\tilde v^{\mathsf T}(M\uparrow)\tilde v<0$ for the cast matrix $M\uparrow$.
--
--   Indeed both the dot product and the matrix–vector product commute with the ring homomorphism $\mathbb Q\to\mathbb R$: casting commutes with finite sums and products, so the real quadratic form of the cast is the cast of the rational quadratic form, and casting preserves strict inequalities.
--
--   This is the direction of the transport needed for the *reject* branch of the PSD oracle: when the rational elimination procedure emits a rational vector of negative quadratic form, that vector is also a witness over the reals, so the real matrix is not positive semidefinite.
-- source:
--   Casting commutes with finite sums and products (RingHom.map_dotProduct / map_mulVec); transport step for the rational PSD oracle of the MAXCUT SDP.

import Mathlib
import Definitions.Def_ModernConvex_SchurFormRat

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **A rational certificate is a real certificate.** -/
theorem cast_quadform_neg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    (h : v ⬝ᵥ (M *ᵥ v) < 0) :
    (fun i => (v i : ℝ)) ⬝ᵥ (M.map (fun q : ℚ => (q : ℝ)) *ᵥ (fun i => (v i : ℝ))) < 0 := by sorry

end ModernConvex.Relaxations
