-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_coherent_extension_orthogonal_eta_of_mem_Sset
-- name    : OddOrder.Peterfalvi.S15.coherent_extension_orthogonal_eta_of_mem_Sset
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:22.231759+00:00
-- url     : https://prove2.me/theorems/484ef77c-8e67-4c8f-8f69-7e47b0d6bb47
-- title:
--   Peterfalvi (13.19.b): $\mathcal L^{\tau_1}$ is orthogonal to the $\eta$-grid
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume no maximal subgroup of $G$ is of type V. Let $L\le G$ carry `dataL : TypeICoherent78Data L` with coherent extension $\tau_1=$ `dataL.coh.extension`, and let $\varphi\in$ `dataL.typeIHyp.Sset` be a class function on $L$. Then for all $i<q$, $j<p$,
--
--   $$\langle \varphi^{\tau_1},\ \eta_{ij}\rangle=0 .$$
--
--   This is (13.19.b), proved via rigidity (3.8) of the $\eta$-grid together with the support statement (13.19.a).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTGrid.lean#L666-L724

import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
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
set_option backward.isDefEq.respectTransparency false in

theorem coherent_extension_orthogonal_eta_of_mem_Sset [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (dataL.coh.extension φ) (hyp.eta i j) = 0 := by sorry

end OddOrder.Peterfalvi.S15
