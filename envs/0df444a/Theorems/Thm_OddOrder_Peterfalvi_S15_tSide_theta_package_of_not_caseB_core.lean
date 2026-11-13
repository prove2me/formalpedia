-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_tSide_theta_package_of_not_caseB_core
-- name    : OddOrder.Peterfalvi.S15.tSide_theta_package_of_not_caseB_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:08:10.177729+00:00
-- url     : https://prove2.me/theorems/e4124c09-ca97-48c3-988f-e7832843f708
-- title:
--   Peterfalvi (13.3.b,c) for $T$: the $\theta$-package when the Case B conclusion fails (Core form)
-- statement:
--   Let $G$ be a minimal simple group of odd order (`IsMinimalSimpleOdd G`), and let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration for $G$: two maximal subgroups $S,T$ with $W=S\cap T=W_1W_2$ cyclic, $|W_1|=q$, $|W_2|=p$ ($p,q$ odd primes), $P=S_F$ and $Q=T_F$ the maximal nilpotent normal Hall subgroups, complements $U,V$ with $S'=PU$, $T'=QV$, $C=C_U(P)$, $D=C_V(Q)$, $|U|=uc$, $|V|=vd$, together with the associated character grids $\eta_{ij}$, $\mu_{ij}$, $\nu_{ij}$ ($i<q$, $j<p$). Let `core : CharacterDegreeCore hyp`, `lam : LambdaClusterData hyp` and `pins : NuGridSupplyData hyp`. Assume the failure of the conclusion of (13.4), namely
--
--   $$\neg\big(D=1\ \wedge\ v=\tfrac{q^p-1}{q-1}\ \wedge\ |Q|=q^p\big)$$
--
--   (with natural-number division). Then there exist a class function $\theta_T$ on $T$, indices $r,r'<q$, a sign $\delta'\in\{1,-1\}$ and a class function $\theta_G$ on $G$ such that
--
--   - $\mathrm{supp}\big(\theta_T-\sum_{j<p}\nu_{rj}\big)\subseteq\{z\in T: z\in QD,\ z\ne1\}$;
--   - $\mathrm{Ind}_T^G\big(\theta_T-\sum_{j<p}\nu_{rj}\big)=\theta_G-\delta'\sum_{j<p}\eta_{r'j}$;
--   - $\langle\eta_{ij},\theta_G\rangle=0$ for all $i<q$, $j<p$;
--   - $\langle\lambda^{\tau_1},\theta_G\rangle=0$, where $\lambda^{\tau_1}=$ `core.tau1S lam.lambda`.
--
--   This is the $T$-side $\theta$-package of (13.3.b,c), used together with (13.4) to rule out the non-Case-B situation.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeSupply.lean#L770-L1098

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped FiniteInduce in

theorem tSide_theta_package_of_not_caseB_core [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (pins : NuGridSupplyData hyp)
    (_hne : ¬ (hyp.D = ⊥ ∧ hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1) ∧
      Nat.card ↥hyp.Q = hyp.q ^ hyp.p)) :
    ∃ (θT : ClassFunction ↥hyp.T ℂ) (r r' : Fin hyp.q) (δ' : ℤ) (θG : ClassFunction G ℂ),
      (δ' = 1 ∨ δ' = -1) ∧
      ((θT - ∑ j : Fin hyp.p, hyp.nu r j).support ⊆
        {z : ↥hyp.T | (z : G) ∈ hyp.Q ⊔ hyp.D ∧ z ≠ 1}) ∧
      (ClassFunction.induce hyp.T (θT - ∑ j : Fin hyp.p, hyp.nu r j)
        = θG - (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r' j) ∧
      (∀ (i : Fin hyp.q) (j : Fin hyp.p), ClassFunction.inner (hyp.eta i j) θG = 0) ∧
      ClassFunction.inner (core.tau1S lam.lambda) θG = 0 := by sorry

end OddOrder.Peterfalvi.S15
