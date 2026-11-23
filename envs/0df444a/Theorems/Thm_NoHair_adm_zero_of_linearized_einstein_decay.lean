-- Prove2me | Theorems.Thm_NoHair_adm_zero_of_linearized_einstein_decay
-- name    : NoHair.adm_zero_of_linearized_einstein_decay
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:52:48.937417+00:00
-- url     : https://prove2.me/theorems/5b32451b-5eb9-4ada-a688-167ce672bb4c
-- title:
--   Vanishing ADM flux from decay of the linearized Einstein tensor
-- statement:
--   Suppose a Cartesian tensor is smooth outside a ball in three-space. If the divergence of its ADM potential decays like $O(r^{-4})$, then its ADM surface flux tends to zero. A cutoff supplies a globally smooth extension without affecting large spheres. The exact finite-radius flux identity then bounds the integral by $O(r^{-1})$.
-- source:
--   P. Miao and L.-F. Tam, Evaluation of the ADM mass and center of mass via the Ricci tensor, Proc. Amer. Math. Soc. 144 (2016), pp. 753–761, Theorem 1.1(a) and the Euclidean integration-by-parts identity in the proof of Theorem 2.1, equations (2.2)–(2.8), https://arxiv.org/abs/1408.3893, https://doi.org/10.1090/proc12726.

import Definitions.Def_NoHair_linearADMFlux

open Set Filter MeasureTheory NoHair
open scoped ContDiff Manifold Topology

theorem NoHair.adm_zero_of_linearized_einstein_decay (k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∃ B : ℝ, ∀ x : ADMPoint, B < ‖x‖ → ∀ i j, ContDiffAt ℝ ∞ (fun y => k y i j) x)
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ i j : Fin 3,
      |negativeTwiceLinearEinstein k i j x| ≤ C / ‖x‖^4) :
    Tendsto (staticADMFlux k) atTop (𝓝 0) := by sorry
