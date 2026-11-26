-- Prove2me | Theorems.Thm_O3_Stage8EuclideanMinimizer_pairing_sub_decomposition
-- name    : O3.Stage8EuclideanMinimizer.pairing_sub_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:15:39.126979+00:00
-- url     : https://prove2.me/theorems/27c8c7f1-b090-4337-acca-2addcf96dddb
-- title:
--   Stage8 Euclidean Minimizer: pairing sub decomposition
-- statement:
--   Affine displacement identity for the coordinate pairing.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L52-L58
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L52-L58

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
set_option autoImplicit true
open O3
open O3.Stage8EuclideanMinimizer

theorem O3.Stage8EuclideanMinimizer.pairing_sub_decomposition {d : ℕ} (s x z x₀ : Point d) :
    pairing s (x - x₀) = pairing s (z - x₀) + pairing s (x - z) := by sorry
