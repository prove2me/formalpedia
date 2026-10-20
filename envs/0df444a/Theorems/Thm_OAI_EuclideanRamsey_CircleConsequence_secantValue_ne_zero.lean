-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_secantValue_ne_zero
-- name    : OAI.EuclideanRamsey.CircleConsequence.secantValue_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:26:17.156324+00:00
-- url     : https://prove2.me/theorems/0fde52c8-6371-4106-9fc9-7dedbcad76b2
-- title:
--   Secant determinants of concyclic points are nonzero in the coordinate field
-- statement:
--   Let $a_0,\dots,a_{s-1}$ be points of the plane $\mathbb R^2$ and $K\subseteq\mathbb R$ the field generated over $\mathbb Q$ by their coordinates. Write $\tilde a_i=(1,a_{i0},a_{i1})$ for the augmented points. Suppose the $a_i$ are pairwise distinct and $|a_m-c|^2=R$ for all $m$. Then for pairwise distinct indices $i,j,k$,
--   $$
--   \Delta(i,j,k)=(a_{j0}-a_{i0})(a_{k1}-a_{i1})-(a_{j1}-a_{i1})(a_{k0}-a_{i0})\ne0\quad\text{in }K .
--   $$
--
--   These nonzero determinants are what make the quadratic isolators of five circle points work.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean#L50-L70

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence

theorem OAI.EuclideanRamsey.CircleConsequence.secantValue_ne_zero {s : ℕ} (a : Fin s → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secantValue a i j k ≠ 0 := by sorry
