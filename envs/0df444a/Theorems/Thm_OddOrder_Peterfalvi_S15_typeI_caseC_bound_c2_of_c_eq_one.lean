-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_typeI_caseC_bound_c2_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.typeI_caseC_bound_c2_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:26:43.019648+00:00
-- url     : https://prove2.me/theorems/3c93b34a-4891-4d9c-8c0d-5c9b61c70708
-- title:
--   Peterfalvi (13.19.c), case (c2): a nonzero $\eta$-pairing forces $p\le e$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume no maximal subgroup of $G$ is of type V and $c=1$. Let $L\le G$ be a subgroup carrying `dataL : TypeICoherent78Data L` (type I coherence data with (7.8) bookkeeping; its characters are $\zeta_0,\dots$, its coherent extension is $\tau_1=$ `dataL.coh.extension`, and $e=[L:L_F]$ with $L_F=$ `maxNilpotentNormalHall L`). Let $n_L$ be an integer with $\langle\beta_L^{\tau}(\zeta_0),\eta_{01}\rangle=n_L$ (notation as in `typeIBetaL dataL.typeIHyp`), and suppose $n_L\ne0$. Then
--
--   $$p\ \le\ [L:L_F]=e .$$
--
--   This is the bound for case (c2) of (13.19.c) obtained from a Bessel inequality over the orthonormal $\eta_{0j}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT.lean#L216-L352

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
set_option backward.isDefEq.respectTransparency false in

theorem typeI_caseC_bound_c2_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nL : ℤ)
    (hnL : ClassFunction.inner (typeIBetaL dataL.typeIHyp (dataL.zeta 0))
        (hyp.eta ⟨0, hyp.q_prime.pos⟩ ⟨1, by have := hyp.three_le_p; omega⟩) = (nL : ℂ))
    (hnL0 : nL ≠ 0) :
    hyp.p ≤ ((maxNilpotentNormalHall L).subgroupOf L).index := by sorry

end OddOrder.Peterfalvi.S15
