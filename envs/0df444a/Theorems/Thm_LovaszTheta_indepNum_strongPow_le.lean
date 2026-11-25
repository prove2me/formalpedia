-- Prove2me | Theorems.Thm_LovaszTheta_indepNum_strongPow_le
-- name    : LovaszTheta.indepNum_strongPow_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T14:37:17.186172+00:00
-- url     : https://prove2.me/theorems/61a355ad-da95-40f5-bab7-014920c3847d
-- title:
--   Lovasz Theta: indep Num strong Pow le
-- statement:
--   **Lovász (1979), multiplicativity.** The same bound holds for strong powers, with `t^k`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L119-L146
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/ThetaLib/Theta.lean#L119-L146

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}

theorem LovaszTheta.indepNum_strongPow_le [Finite V] (G : SimpleGraph V) {d : ℕ} {u : V → Fin d → ℝ}
    (hu : IsOrthonormalRep G u) {c : Fin d → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) (k : ℕ) :
    ((strongPow G k).indepNum : ℝ) ≤ t ^ k := by sorry
