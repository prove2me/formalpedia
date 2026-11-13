-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_caseB_order_u_of_analytic_inequality
-- name    : OddOrder.Peterfalvi.S15.caseB_order_u_of_analytic_inequality
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:00:39.381654+00:00
-- url     : https://prove2.me/theorems/80276af2-8c36-46e4-a31b-ae2edc7d5e30
-- title:
--   Peterfalvi (13.15): the value of $u$ in Case B in terms of $(p^q-1)/(p-1)$
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Assume the analytic inequality (13.10) in the form
--
--   $$\frac{u}{c}>\frac{m\,p^{q-1}}{q}\quad(\text{in }\mathbb Q,\ m=\text{`hyp.m`}),$$
--
--   and let `chief : ChiefFactorData` and `caseB : CliffordCaseBData` be Clifford case (b) data for the Section 11 character data of $S$. Then (natural-number division)
--
--   $$p\equiv1\ (\mathrm{mod}\ q)\ \Rightarrow\ u=\frac{p^q-1}{q(p-1)},\qquad p\not\equiv1\ (\mathrm{mod}\ q)\ \Rightarrow\ u=\frac{p^q-1}{p-1}.$$
--
--   The extra factor $q$ occurs precisely in the branch $p\equiv1\pmod q$; this is the final Singer cyclotomic order of $u$ in (13.15).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CaseBOrder.lean#L289-L386

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

theorem caseB_order_u_of_analytic_inequality [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief)) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by sorry

end OddOrder.Peterfalvi.S15
