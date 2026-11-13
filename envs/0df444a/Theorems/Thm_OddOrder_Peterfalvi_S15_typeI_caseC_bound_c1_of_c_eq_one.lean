-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_typeI_caseC_bound_c1_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.typeI_caseC_bound_c1_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:43.955023+00:00
-- url     : https://prove2.me/theorems/33aa9ed2-ff7a-426e-8ae9-0851aca24dcc
-- title:
--   Peterfalvi (13.19.c), case (c1): a nonzero $S$-pairing forces $(|H|-1)/e\le(u-1)/q$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume no maximal subgroup of $G$ is of type V and $c=1$. Let $L\le G$ be a subgroup carrying `dataL : TypeICoherent78Data L` (type I coherence data with (7.8) bookkeeping; its characters are $\zeta_0,\dots$, its coherent extension is $\tau_1=$ `dataL.coh.extension`, and $e=[L:L_F]$ with $L_F=$ `maxNilpotentNormalHall L`). Let $n_S$ be an integer with $\langle\beta_S^{\tau},\zeta_0^{\tau_1}\rangle=n_S$ (where $\beta_S^\tau=$ `tauSbetaGrid hG hyp`), and suppose $n_S\ne0$. Then, in $\mathbb Q$,
--
--   $$\frac{|H_L|-1}{[L:L_F]}\ \le\ \frac{u-1}{q},$$
--
--   where $H_L=$ `dataL.typeIHyp.H` is the subgroup $H$ of the type I setup of $L$.
--
--   This is case (c1) of (13.19.c), derived from the bound (13.18.d) on the projection of $\Gamma_S$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT.lean#L556-L696

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

theorem typeI_caseC_bound_c1_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) (nS : ℤ)
    (hnS : ClassFunction.inner (tauSbetaGrid hG hyp) (dataL.coh.extension (dataL.zeta 0))
        = (nS : ℂ))
    (hnS0 : nS ≠ 0) :
    (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ)
        / (((maxNilpotentNormalHall L).subgroupOf L).index : ℚ) ≤
      ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ)) := by sorry

end OddOrder.Peterfalvi.S15
