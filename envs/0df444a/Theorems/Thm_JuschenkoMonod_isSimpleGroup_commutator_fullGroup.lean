-- Prove2me | Theorems.Thm_JuschenkoMonod_isSimpleGroup_commutator_fullGroup
-- name    : JuschenkoMonod.isSimpleGroup_commutator_fullGroup
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-29T17:30:40.888503+00:00
-- url     : https://prove2.me/theorems/60d9e2ce-020c-4a90-8a38-c6e9b6bb7ddd
-- title:
--   Matui, Theorem 4.9 — the commutator subgroup of [[T]] is simple for every minimal Cantor system
-- statement:
--   Let $T$ be a minimal homeomorphism of a Cantor space $C$. Then the commutator subgroup $[[[T]], [[T]]]$ of the topological full group $[[T]]$ is a simple group (nontrivial, with no normal subgroups other than itself and the trivial group).
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 775, Matui's simplicity theorem, which cites Matui, H., Some remarks on topological full groups of Cantor minimal systems, Internat. J. Math. 17 (2006) 231–251, https://doi.org/10.1142/S0129167X06003448, Theorem 4.9

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

theorem isSimpleGroup_commutator_fullGroup (C : Type*) [TopologicalSpace C]
    (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C) (hT : IsMinimal T) :
    IsSimpleGroup (commutator (fullGroup T)) := by
  sorry

end JuschenkoMonod
