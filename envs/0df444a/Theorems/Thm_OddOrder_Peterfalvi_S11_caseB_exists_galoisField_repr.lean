-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S11_caseB_exists_galoisField_repr
-- name    : OddOrder.Peterfalvi.S11.caseB_exists_galoisField_repr
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T12:31:27.930179+00:00
-- url     : https://prove2.me/theorems/d5492acc-4c74-4720-ad42-7502db47d346
-- title:
--   Peterfalvi (9.7.b): $\bar U$ acts on $\bar H=H/N$ as multiplication on $GF(p^q)$
-- statement:
--   Let $G$ be a finite group and $M\le G$ a subgroup, with the Peterfalvi Types I--V setup `data : TypesIIIIIIVSetup M` (with subgroup $H$ and parameter $q=$ `data.q`), a chief-factor datum `chief : ChiefFactorData data` (with $p=$ `chief.p` prime, $N$, $H_0$), and the Section 11 character data `chars`. Suppose the data are in Clifford case B (`caseB : CliffordCaseBData chars`). Let $\bar U=$ `MonoidHom.range (uActionHom data chief)` be the image of $U$ acting on $\bar H=H/N$. Then there exist an additive isomorphism $e:\bar H\to GF(p^q)$ (`GaloisField p q`) and an injective homomorphism $\mu:\bar U\to GF(p^q)^\times$ such that
--   $$e(u\cdot x)=\mu(u)\,e(x)\qquad\text{for all }u\in\bar U,\ x\in\bar H .$$
--
--   This is Peterfalvi (9.7.b), the field model of the faithful irreducible action in case B.
--
--   **Formalization Note.** $\bar H$ is written additively via `Additive`; the `Fact chief.p.Prime` instance is supplied inside the statement with `letI`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_GaloisFieldModel.lean#L29-L137

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
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldAut
import Definitions.Def_OddOrder_Peterfalvi_S11_GaloisFieldModel
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory OddOrder.RepresentationTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped IsMulCommutative

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in

theorem caseB_exists_galoisField_repr [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    letI : Fact chief.p.Prime := ⟨chief.p_prime⟩
    ∃ (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
      (μ : ↥(MonoidHom.range (uActionHom data chief)) →*
        (GaloisField chief.p data.q)ˣ),
      Function.Injective μ ∧
      ∀ (u : ↥(MonoidHom.range (uActionHom data chief)))
        (x : ↥data.H ⧸ chief.N),
        e (Additive.ofMul ((MonoidHom.range (uActionHom data chief)).subtype u x)) =
          ((μ u : (GaloisField chief.p data.q)ˣ) : GaloisField chief.p data.q) *
            e (Additive.ofMul x) := by sorry

end OddOrder.Peterfalvi.S11
