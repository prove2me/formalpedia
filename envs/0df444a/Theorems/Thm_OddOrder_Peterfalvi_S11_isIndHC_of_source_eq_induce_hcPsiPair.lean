-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S11_isIndHC_of_source_eq_induce_hcPsiPair
-- name    : OddOrder.Peterfalvi.S11.isIndHC_of_source_eq_induce_hcPsiPair
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T12:11:08.053673+00:00
-- url     : https://prove2.me/theorems/b233b217-4a9d-41f4-a68b-cff1284a870a
-- title:
--   Peterfalvi Section 11: stages-flattening for characters induced from $\mathrm{hcPsiPair}$
-- statement:
--   Let $G$ be a finite group and $M\le G$ a subgroup, with the Peterfalvi Types I--V setup `data : TypesIIIIIIVSetup M` (with subgroup $H$ and parameter $q=$ `data.q`), a chief-factor datum `chief : ChiefFactorData data` (with $p=$ `chief.p` prime, $N$, $H_0$). Suppose $\zeta'$ is an irreducible character of $HU$ (`huSub data`) with
--   $$\zeta'=\mathrm{Ind}_{HC}^{HU}\ \texttt{hcPsiPair}(\bar\theta,\lambda)$$
--   for some homomorphisms $\bar\theta:H/N\to\mathbb C^\times$ and $\lambda:C\to\mathbb C^\times$. Then there exists a class function $\psi$ on the image (in $G$) of the corresponding subgroup $HC$ of $M$ such that $\psi$ is an irreducible character, $\psi(1)=1$ (so $\psi$ is linear), and
--   $$\texttt{induceHU data}(\zeta')=\mathrm{Ind}\,\psi .$$
--
--   Thus a member of the family $\mathcal S$ whose source is induced from a pair character is induced from a linear character of the $M$-level $HC$; it is the pair analogue of the corresponding statement for `hcPsi`.
--
--   **Formalization Note.** Fintype and `Invertible (Nat.card ·: ℂ)` instances for $M$, $HU$ and the subgroups involved are explicit hypotheses.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHomBasic.lean#L502-L614

import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CaseBXi
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHomBasic

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in

theorem isIndHC_of_source_eq_induce_hcPsiPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    [Fintype ↥M] [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {ζ' : IrreducibleCharacter ↥(huSub data)}
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ} {lam : ↥(cInHu data chief) →* ℂˣ}
    (hζ'eq : (ζ' : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
          (hcPsiPair chief θbar lam).toClassFunction) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      induceHU data (ζ' : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by sorry

end OddOrder.Peterfalvi.S11
