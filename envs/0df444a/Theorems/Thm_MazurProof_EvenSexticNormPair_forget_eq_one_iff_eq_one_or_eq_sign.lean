-- Prove2me | Theorems.Thm_MazurProof_EvenSexticNormPair_forget_eq_one_iff_eq_one_or_eq_sign
-- name    : MazurProof.EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:14:26.650119+00:00
-- url     : https://prove2.me/theorems/5b4a4b4f-2d5e-4dde-9342-23a600f07578
-- title:
--   Mazur 13 port: forget_eq_one_iff_eq_one_or_eq_sign
-- statement:
--   If the base group has only two square roots of one, the forgetting kernel has at most the identity and one sign class.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/EvenSexticNormPair.lean#L332

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.EvenSexticNormPair
variable {A B : Type*} [CommGroup A] [CommGroup B]

theorem MazurProof.EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign (N : A →* B) (e : B →* A) (norm_scalar : ∀ q : B, N (e q) = q ^ 6) (σ : B) (hσ : σ ^ 2 = 1) (sqOne : ∀ ε : B, ε ^ 2 = 1 → ε = 1 ∨ ε = σ) (z : FullTarget N e norm_scalar) : forget N e norm_scalar z = 1 ↔ z = 1 ∨ z = QuotientGroup.mk' (fullGauge N e norm_scalar) (signPair N σ hσ) := by sorry
