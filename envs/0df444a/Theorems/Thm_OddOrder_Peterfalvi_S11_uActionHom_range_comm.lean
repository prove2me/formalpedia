-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S11_uActionHom_range_comm
-- name    : OddOrder.Peterfalvi.S11.uActionHom_range_comm
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T12:18:36.606736+00:00
-- url     : https://prove2.me/theorems/aac80c14-67cf-4a1f-afa7-1522a04a0584
-- title:
--   Peterfalvi (8.5.b)/(9.7): the image $\bar U$ of the $U$-action on $H/N$ is abelian
-- statement:
--   Let $G$ be a finite group and $M\le G$ a subgroup, with the Peterfalvi Types I--V setup `data : TypesIIIIIIVSetup M` (with subgroup $H$ and parameter $q=$ `data.q`), a chief-factor datum `chief : ChiefFactorData data` (with $p=$ `chief.p` prime, $N$, $H_0$).
--
--   Then the image $\bar U=$ `MonoidHom.range (uActionHom data chief)` of $U$ in $\mathrm{Aut}(H/N)$ is commutative: $st=ts$ for all $s,t\in\bar U$.
--
--   The proof uses that commutators of $U$ centralize $H$ (Peterfalvi (8.5.b)), so they act trivially on $H/N$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean#L213-L254

import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerLineBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearImprimitiveBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LineScalarCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AInvariantSubrep
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation

namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory OddOrder.GroupTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk')

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem uActionHom_range_comm [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    (chief : ChiefFactorData data) (s t : ↥(MonoidHom.range (uActionHom data chief))) :
    s * t = t * s := by sorry

end OddOrder.Peterfalvi.S11
