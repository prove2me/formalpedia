-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_dadeSupport_betaGrid_disjoint_support_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.dadeSupport_betaGrid_disjoint_support_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:24:17.961214+00:00
-- url     : https://prove2.me/theorems/0d581636-522f-4e80-b970-05cebb39cdb4
-- title:
--   Peterfalvi (13.19.a): support disjointness of type I Dade data and the $S$-side image of $\beta_j$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume no maximal subgroup of $G$ is of type V and $c=1$. Let $L\le G$ and let `typeISetup : S14.Hypothesis L` be a type I setup for $L$ with Dade support `typeISetup.dadeData.dade.dadeSupport`. Let $\chi$ be a class function on $G$ whose support lies in that Dade support, and let $j<p$ with $j\ne0$. Let $\tau_S$ be the Dade isometry map for `hyp.dadeHypS0 hG`. Then
--
--   $$\mathrm{supp}(\chi)\ \cap\ \mathrm{supp}\big(\tau_S(\beta_j)\big)=\emptyset,\qquad \beta_j=\text{`betaGrid hyp j`}.$$
--
--   This is the support disjointness of (13.19.a) in arbitrary column form, resting on $|H|$ being coprime to $pq$ by (8.17.a).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTGrid.lean#L392-L511

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

theorem dadeSupport_betaGrid_disjoint_support_of_c_eq_one [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    {L : Subgroup G} (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L)
    (χ : ClassFunction G ℂ)
    (hχ : χ.support ⊆ typeISetup.dadeData.dade.dadeSupport)
    (j : Fin hyp.p) (hj : (j : ℕ) ≠ 0) :
    Disjoint χ.support
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 _hG)
        ((hyp.dadeHypS0 _hG).fullDadeIsometryData)
        (betaGrid hyp j)).support := by sorry

end OddOrder.Peterfalvi.S15
