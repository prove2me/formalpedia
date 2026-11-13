-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_typeI_caseC_dichotomy_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.typeI_caseC_dichotomy_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:26:46.406361+00:00
-- url     : https://prove2.me/theorems/62e74986-42fe-4875-aad0-7ac1c749fe59
-- title:
--   Peterfalvi (13.19.c): the $S$-side dichotomy (c1) or (c2) when $c=1$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume no maximal subgroup of $G$ is of type V and $c=1$. Let $L\le G$ be a subgroup carrying `dataL : TypeICoherent78Data L` (type I coherence data with (7.8) bookkeeping; its characters are $\zeta_0,\dots$, its coherent extension is $\tau_1=$ `dataL.coh.extension`, and $e=[L:L_F]$ with $L_F=$ `maxNilpotentNormalHall L`). Let $\varphi$ be a class function on $L$ in `dataL.typeIHyp.Sset` with $\varphi(1)=e=[L:L_F]$. Then one of the following holds:
--
--   - (c1) the inner product $\langle\beta_S^{\tau},\varphi^{\tau_1}\rangle$ is an odd integer (`OddIntegerInner`), and $\dfrac{|H_L|-1}{e}\le\dfrac{u-1}{q}$ (in $\mathbb Q$, $H_L=$ `dataL.typeIHyp.H`);
--   - (c2) for every $j<p$ with $j\ne0$ the inner product $\langle\beta_L^{\tau}(\varphi),\eta_{0j}\rangle$ is an odd integer, and $p\le e$.
--
--   This combines the $\zeta_0$-based parity core and case bounds of (13.19.c) via two $\varphi$-invariance bridges.
--
--   **Formalization Note**. `OddIntegerInner a b` is the project's predicate expressing that $\langle a,b\rangle$ is an odd integer.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT.lean#L698-L759

import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem typeI_caseC_dichotomy_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (_hφ : φ ∈ dataL.typeIHyp.Sset)
    (_hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    (OddIntegerInner (tauSbetaGrid _hG hyp) (dataL.coh.extension φ) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
          / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner (typeIBetaL dataL.typeIHyp φ) (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧
        hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index) := by sorry

end OddOrder.Peterfalvi.S15
