-- Prove2me | Theorems.Thm_MaxCompForest_eq_3_8_covariance
-- name    : MaxCompForest.eq_3_8_covariance
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:28.238453+00:00
-- url     : https://prove2.me/theorems/fa34b1c7-ca4b-4b02-95c3-c2b9ff38313a
-- title:
--   Eq. (3.8) — the determinant equals the covariance objective $W(F)$
-- statement:
--   Let $H$ be an edge-labelled graph with positive multipliers $c_e$, positive vertex masses $d_v$ and feature vectors $\phi_v\in\mathbb R^r$, collected as the columns of $\mathbf F$. For every forest $F$,
--   $$
--   \det\Big(C_F^{1/2}B_F^{\top}(D^{-1}+\mathbf F^{\top}\mathbf F)B_FC_F^{1/2}\Big)=W(F),
--   $$
--   with $W$ the covariance objective (3.7). For a cyclic set $F$ the determinant is zero.
--
--   This identity expresses the electrical-response determinant through the components of the forest, so that the terminal optimizer can build it from partial trees.
--
--   Differences from the source:
--   - generalization: rational feature columns $\phi_v\in\mathbb Q^r$ and rational multipliers → real feature columns and real multipliers; reason: the identity is algebraic; rational data are a special case
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (3.5)–(3.8) p.16; p.17

import Mathlib
import Definitions.Def_MaxCompForest_respForm
import Definitions.Def_MaxCompForest_featGram
import Definitions.Def_MaxCompForest_covObj
import Definitions.Def_MaxCompForest_IsForest
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

/-- **Eq. (3.8)**, for every forest, with arbitrary positive masses; the determinant vanishes on a cyclic set.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (3.5)–(3.8) p.16, p.17 for the cyclic case. -/
theorem eq_3_8_covariance {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : WGraph V E) (d : V → ℝ) (hd : ∀ v, 0 < d v) {r : ℕ}
    (φ : V → EuclideanSpace ℝ (Fin r)) (F : Finset E) :
    (IsForest G F → (respForm G d (featGram φ) F).det = covObj G d φ F) ∧
      (¬ IsForest G F → (respForm G d (featGram φ) F).det = 0) := by sorry

end MaxCompForest
