-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S11_caseA_blockScalarFacts
-- name    : OddOrder.Peterfalvi.S11.caseA_blockScalarFacts
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T12:19:22.828199+00:00
-- url     : https://prove2.me/theorems/01519338-9f0f-4563-96b2-e3e8340601ee
-- title:
--   Peterfalvi (9.7.a): block-scalar embedding of $\bar U$ and the bound $u\mid a^{q-1}$
-- statement:
--   Let $G$ be a finite group and $M\le G$ a subgroup, with the Peterfalvi Types I--V setup `data : TypesIIIIIIVSetup M` (with subgroup $H$ and parameter $q=$ `data.q`), a chief-factor datum `chief : ChiefFactorData data` (with $p=$ `chief.p` prime, $N$, $H_0$), and the Section 11 character data `chars`. Suppose the data are in Clifford case A (`caseA : CliffordCaseAData chars`); let $u=$ `chars.u` and $\bar U=$ `MonoidHom.range (uActionHom data chief)`. Then both of the following hold:
--
--   1. there is an injective homomorphism $\psi:\bar U\to\big(\mathbb Z/p\big)^{\times\,(q-1)}$, i.e. into the functions $\mathrm{Fin}(q-1)\to(\mathbb Z/p)^\times$ with pointwise multiplication;
--   2. there is $a\in\mathbb N$ with $a\mid p-1$ and $u\mid a^{\,q-1}$.
--
--   This is Peterfalvi (9.7.a); the embedding in (1) is later restricted to a Sylow subgroup in the argument of (14.6).
--
--   **Formalization Note.** $p-1$ and $q-1$ are natural-number subtractions (with $p,q\ge1$ in practice).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_ImprimitiveUBound.lean#L294-L440

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

open scoped Classical in

theorem caseA_blockScalarFacts [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    (caseA : CliffordCaseAData chars) :
    (∃ ψ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (Fin (data.q - 1) → (ZMod chief.p)ˣ),
      Function.Injective ψ) ∧ ∃ a : ℕ, a ∣ chief.p - 1 ∧ chars.u ∣ a ^ (data.q - 1) := by sorry

end OddOrder.Peterfalvi.S11
