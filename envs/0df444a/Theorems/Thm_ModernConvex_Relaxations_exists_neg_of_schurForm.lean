-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_exists_neg_of_schurForm
-- name    : ModernConvex.Relaxations.exists_neg_of_schurForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:30:12.7978+00:00
-- url     : https://prove2.me/theorems/d34cac9d-602b-495a-b271-47e230c16c94
-- title:
--   A negative Schur form at a positive pivot yields a direction of negative quadratic form
-- statement:
--   **A negative Schur form yields a certificate of non-semidefiniteness.**
--
--   Let $M$ be real symmetric with $M_{ii}>0$, and suppose the Schur form $Q_i$ takes a negative value at some $w$. Then there is $v$ with $v^{\mathsf T}Mv<0$.
--
--   The construction is explicit: keep the coordinates of $w$ off $i$ and set
--   $$v_i=-\frac{1}{M_{ii}}\sum_{j\ne i}M_{ij}w_j .$$
--   Because $Q_i$ only involves coordinates $j\ne i$, we have $Q_i(v)=Q_i(w)<0$, and by the choice of $v_i$ the square term in the completing-the-square identity vanishes. Hence $v^{\mathsf T}Mv=Q_i(w)<0$.
--
--   This is the "reject" arm of the elimination step, and it is what makes the oracle's certificate explicit and rational: if $w$ is rational then so is $v$.
-- source:
--   Completing the square at a positive pivot; reject arm of the symmetric-elimination PSD test, producing the separating direction.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **A negative Schur form gives a certificate.** -/
theorem exists_neg_of_schurForm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : 0 < M i i) (w : Fin n → ℝ) (hw : schurForm M i w < 0) :
    ∃ v : Fin n → ℝ, v ⬝ᵥ (M *ᵥ v) < 0 := by sorry

end ModernConvex.Relaxations
