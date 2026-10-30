-- Prove2me | Theorems.Thm_JuschenkoMonod_infinite_commutator_fullGroup_and_fg_iff_conj_subshift
-- name    : JuschenkoMonod.infinite_commutator_fullGroup_and_fg_iff_conj_subshift
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:31:03.603816+00:00
-- url     : https://prove2.me/theorems/1a4bdcae-2e75-42d5-a660-c382e41b9684
-- title:
--   Matui — the commutator subgroup of [[T]] is infinite, and finitely generated iff (T, C) is conjugate to a minimal subshift
-- statement:
--   Let $T$ be a minimal homeomorphism of a Cantor space $C$. Then the commutator subgroup of $[[T]]$ is infinite, and it is finitely generated if and only if there are a finite alphabet $\{0, \dots, m-1\}$, a subshift $S \subseteq \{0, \dots, m-1\}^{\mathbf Z}$ (closed and shift-invariant) on which the shift $\tau$, $(\tau x)_i = x_{i+1}$, is minimal, and a homeomorphism $h\colon C \to S$ with $h \circ T = \tau \circ h$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 775, Matui's finite generation criterion, which cites Matui, H., Some remarks on topological full groups of Cantor minimal systems, Internat. J. Math. 17 (2006) 231–251, https://doi.org/10.1142/S0129167X06003448

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem infinite_commutator_fullGroup_and_fg_iff_conj_subshift (C : Type*) [TopologicalSpace C]
    (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C) (hT : IsMinimal T) :
    Infinite (commutator (fullGroup T)) ∧
      (Group.FG (commutator (fullGroup T)) ↔
        ∃ (m : ℕ) (S : CantorSystems.Subshift ℤ (Fin m)) (h : C ≃ₜ S),
          IsMinimal (shiftHomeomorph S) ∧ ∀ x : C, h (T x) = shiftHomeomorph S (h x)) := by
  sorry

end JuschenkoMonod
