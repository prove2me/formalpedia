-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_NormSet_normOneFrobenius_isFrobeniusGroup
-- name    : OddOrder.BG.AppC.NormSet.normOneFrobenius_isFrobeniusGroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T07:37:54.063761+00:00
-- url     : https://prove2.me/theorems/baf14625-03fc-4e43-a742-0dfbda94fd3c
-- title:
--   The group $P\rtimes U$ of BG Appendix C is a Frobenius group
-- statement:
--   Let $p$ be a prime and $q>1$ a natural number. Let $H=P\rtimes U$ be the concrete group `normOneFrobeniusGroup p q`, where $P=(\mathbb{F}_{p^q},+)$ is the additive kernel and $U$ is the group of norm-one units of $\mathbb{F}_{p^q}$, acting on $P$ by multiplication. Then $H$ is a Frobenius group with kernel $P$ and complement $U$ (that is, `IsFrobeniusGroup H P U`: $P$ is a nontrivial normal subgroup, $U$ is a nontrivial complement, and no nonidentity element of $U$ commutes with a nonidentity element of $P$).
--
--   This records the structure of the model group $H$ used throughout Appendix C of Bender--Glauberman.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_NormOneInduce.lean#L206-L240

import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
import Definitions.Def_OddOrder_BG_AppC_NormOneInduce
import Mathlib.Data.Set.Card.Arithmetic

namespace OddOrder.BG.AppC.NormSet

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable (p q : ℕ)

theorem normOneFrobenius_isFrobeniusGroup [Fact p.Prime] (hq : 1 < q) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup (normOneFrobeniusGroup p q)
      (normOneFrobeniusKernel p q) (normOneFrobeniusComplement p q) := by sorry

end OddOrder.BG.AppC.NormSet
