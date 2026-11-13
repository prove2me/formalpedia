-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_exists_muT_index_core_of_base_condition
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.exists_muT_index_core_of_base_condition
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:01:08.010028+00:00
-- url     : https://prove2.me/theorems/ba3d5104-530c-4f63-aa69-6226560f159f
-- title:
--   Peterfalvi (13.8) for $T$: a distinguished index with $\langle\tau\psi_{i_1},\eta_{10}\rangle=\pm1$ over a chosen base
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume moreover: no maximal subgroup of $G$ is of type V (`hnoV`); `pins : NuGridSupplyData hyp`; $vd\ne1$; $T$ is of type P (`IsTypeP hyp.T`) with `Tdata : TypePData hyp.T` satisfying `Tdata.U = V`, `Tdata.W1 = W₂`, `Tdata.W2 = W₁`; `chief : ChiefFactorData` for the type-I/II/III/V setup of $T$; $D=1$; $Q$ is commutative. Let $\varphi_0$ be an irreducible character of $Q$ (as a subgroup of $T$) with $Q\not\subseteq\ker\varphi_0$, such that either $\mathrm{Ind}_Q^T\varphi_0$ is irreducible or $\langle(\mathrm{Ind}_Q^T\varphi_0)^{\tau_1},\eta_{10}\rangle=0$ (with $\tau_1$ the honest $T$-side extension `tau1T_ofHonest`). Let $\zeta_0,\dots,\zeta_n$ be the (7.6) family `Q_sharp_hypothesis76_base` of characters of $T$ based at $\mathrm{Ind}_Q^T\varphi_0$ with (7.7.a) coefficients $c_i(\cdot)=$ `cCoeff · i`. Then there exist an index $i_1>0$ and an integer $\delta$ such that:
--
--   - $Q\not\subseteq\ker\zeta_{i_1}$ and $\delta^2=1$;
--   - $c_{i_1}(\eta_{10})=\delta$;
--   - $c_i(\eta_{10})=0$ for every $i>0$, $i\ne i_1$ with $Q\not\subseteq\ker\zeta_i$;
--   - $\|\zeta_{i_1}\|^2=p$ (`zetaNormSq`) and $\zeta_{i_1}(1)=pv$.
--
--   This supplies, on the $T$-side, the distinguished $\nu$-row index needed in the character-degree argument of Peterfalvi Section 13.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean#L64-L631

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

set_option maxHeartbeats 1600000 in
-- The (7.6)-family bookkeeping (constituent expansion + per-index coefficient computation)
-- elaborates as a single large proof term; the default budget covers only part of it.
open OddOrder.Peterfalvi.S11 in
open scoped Classical in
open scoped FiniteInduce in

theorem Hypothesis.exists_muT_index_core_of_base_condition [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hD : hyp.D = ⊥)
    (hQcomm : IsMulCommutative ↥hyp.Q)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T))
    (hφ₀Q : ¬ (((hyp.Q.subgroupOf hyp.T).subgroupOf (hyp.Q.subgroupOf hyp.T) :
        Set ↥(hyp.Q.subgroupOf hyp.T)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)))
    (hφ₀base :
      OddOrder.RepresentationTheory.IsIrreducibleCharacter
          (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
            (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ)) ∨
        ClassFunction.inner
          (hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
            (ClassFunction.induce (hyp.Q.subgroupOf hyp.T)
              (φ₀ : ClassFunction ↥(hyp.Q.subgroupOf hyp.T) ℂ))) hyp.eta10 = 0) :
    ∃ (i₁ : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1)) (δ : ℤ), 0 < i₁ ∧
      ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁)) ∧
      δ ^ 2 = 1 ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i₁ = (δ : ℂ) ∧
      (∀ i : Fin ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).n + 1), 0 < i → i ≠ i₁ →
        ¬ ((hyp.Q.subgroupOf hyp.T : Set ↥hyp.T) ⊆
          OddOrder.Peterfalvi.S03.characterKernel
            ((Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i)) →
        (Q_sharp_hypothesis76_base hG hyp hvd φ₀).cCoeff hyp.eta10 i = 0) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zetaNormSq i₁ = (hyp.p : ℂ) ∧
      (Q_sharp_hypothesis76_base hG hyp hvd φ₀).zeta i₁ 1 = ((hyp.p * hyp.v : ℕ) : ℂ) := by sorry

end OddOrder.Peterfalvi.S15
