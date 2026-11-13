-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_tau1T_ofHonest_nuRow_eta_row
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.tau1T_ofHonest_nuRow_eta_row
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:49:44.274204+00:00
-- url     : https://prove2.me/theorems/b7fbf9e1-9fb4-44b7-9c37-637807a37a63
-- title:
--   Peterfalvi (13.3.c): $\tau_1^T(\nu_r)=\pm\sum_j\eta_{r'j}$ for a nonzero row $r'$
-- statement:
--   Let $G$ be a finite group which is a minimal simple odd-order group, and assume there is no maximal subgroup of $G$ of type V (`hnoV`). Let `hyp` be a Peterfalvi §13 configuration with parameters $p,q,v,d$, subgroup $T$, and let `pins : NuGridSupplyData hyp`. Assume $v d \neq 1$, that $T$ is of type P (`IsTypeP hyp.T`), and let `Tdata : TypePData hyp.T` be a type-$P$ datum whose $U$-, $W_1$-, $W_2$-components are $V$, $W_2$, $W_1$ of `hyp` (`hU`, `hW1`, `hW2`). Let `chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)` be chief-factor data for the associated type I–IV setup on $T$. Write $\tau_1^T$ for the map `hyp.tau1T_ofHonest …` built from all these data. Then for every row index $r \in \{0,\dots,q-1\}$ with $r \neq 0$ there are a row $r' \neq 0$ and an integer $\delta'\in\{1,-1\}$ such that
--   $$\tau_1^T\Bigl(\sum_{j=0}^{p-1}\nu_{rj}\Bigr) \;=\; \delta' \sum_{j=0}^{p-1}\eta_{r'j}.$$
--
--   In the proof of (13.3.c) the generic case is $r'=r$, $\delta'=1$, while for $q=3$ a flip $r' \ne r$, $\delta'=-1$ can occur. This is the $\beta$-form input to the $\theta$-package of (13.4).
--
--   **Formalization Note.** The map `tau1T_ofHonest` is a project-defined function on class functions of $T$ (with values in class functions of $G$); the exact data it depends on are exactly the hypotheses listed above. Scalar multiplication by $\delta'$ is via the cast $\mathbb{Z}\to\mathbb{C}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Tau1T.lean#L106-L162

import Definitions.Def_OddOrder_Peterfalvi_S15_NuRowPin
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in

theorem Hypothesis.tau1T_ofHonest_nuRow_eta_row [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {r : Fin hyp.q} (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) :
    ∃ (r' : Fin hyp.q) (δ' : ℤ), r' ≠ ⟨0, hyp.q_prime.pos⟩ ∧ (δ' = 1 ∨ δ' = -1) ∧
      hyp.tau1T_ofHonest hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          (∑ j : Fin hyp.p, hyp.nu r j)
        = (δ' : ℂ) • ∑ j : Fin hyp.p, hyp.eta r' j := by sorry

end OddOrder.Peterfalvi.S15
