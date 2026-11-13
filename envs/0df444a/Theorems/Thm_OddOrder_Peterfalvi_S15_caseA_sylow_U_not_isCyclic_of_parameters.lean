-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_caseA_sylow_U_not_isCyclic_of_parameters
-- name    : OddOrder.Peterfalvi.S15.caseA_sylow_U_not_isCyclic_of_parameters
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:56:03.359463+00:00
-- url     : https://prove2.me/theorems/103f91e2-e0e3-4efb-bfa6-45fc7dadcd6f
-- title:
--   Peterfalvi (14.6): Sylow subgroups of $U$ at the parameters $q=3$, $u=(p-1)^2/4$ are noncyclic
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `chief : ChiefFactorData` and `caseA : CliffordCaseAData` be a chief-factor datum and a Clifford case (a) datum for the Section 11 character data of $S$. Assume $q=3$ and $u=\dfrac{(p-1)^2}{4}$ (natural-number division). Let $r$ be a prime dividing $\dfrac{p-1}{2}$ and $R$ a Sylow $r$-subgroup of $U$. Then $R$ is not cyclic.
--
--   This is the sharp-parameter noncyclicity statement of (14.6) for the $S$-side $U$, obtained from the Section 11 block-scalar theorem.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean#L936-L983

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem caseA_sylow_U_not_isCyclic_of_parameters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.mkSection11CharacterDataS hG chief))
    (hq : hyp.q = 3) (hu : hyp.u = (hyp.p - 1) ^ 2 / 4)
    {r : ℕ} (hr : r.Prime) (hrhalf : r ∣ (hyp.p - 1) / 2)
    (R : Sylow r ↥hyp.U) : ¬ IsCyclic ↥(R : Subgroup ↥hyp.U) := by sorry

end OddOrder.Peterfalvi.S15
