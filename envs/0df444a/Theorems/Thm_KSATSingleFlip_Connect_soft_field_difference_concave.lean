-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_difference_concave
-- name    : KSATSingleFlip.Connect.soft_field_difference_concave
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:18:22.554324+00:00
-- url     : https://prove2.me/theorems/63d13988-d88c-401a-af30-372b8a03de89
-- title:
--   Concavity of the soft-field gap test f−g
-- statement:
--   The difference f(q)−g(q), for the mass and potential test functions of Section 4.1, is concave on [0,1] and vanishes at the endpoints. This supplies the nontrivial admissible test used in the proof of the Poisson comparison Lemma 4.5.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open KSATSingleFlip.Connect Set
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_difference_concave : ConcaveOn ℝ (Icc 0 1) (fun x => fW x-gW x) ∧
    (fW 0-gW 0 = 0) ∧ (fW 1-gW 1 = 0) := by sorry
