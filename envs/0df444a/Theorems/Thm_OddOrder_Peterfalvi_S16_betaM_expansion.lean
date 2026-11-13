-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_betaM_expansion
-- name    : OddOrder.Peterfalvi.S16.betaM_expansion
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:29:24.983345+00:00
-- url     : https://prove2.me/theorems/c0abc393-7764-4baa-a333-93ee14316e95
-- title:
--   Peterfalvi (14.11.2): if $K\neq V$ then $e=pq$ and $\beta_M^\tau$ is a signed $\eta$-grid sum minus $\chi$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), assume `hncH0C : S13.H0CNoncoherenceRefuter G`, let `hyp` be a Peterfalvi §14 configuration with primes $p,q$ and grid $\eta_{ij}$, and let `Mdata : MHypothesis hyp` with kernel $K$ and complement index $e$. Assume $K\neq V$. Then $e=pq$, and there are signs $\varepsilon_{ij}\in\{1,-1\}$ ($i<q$, $j<p$) and a class function $\chi$ on $G$ such that $|\chi(g)|=|\tau_1\psi(g)|$ for all $g\in G$ and
--   $$\beta_M \;=\; \sum_{i<q}\sum_{j<p}\varepsilon_{ij}\,\eta_{ij}\;-\;\chi,$$
--   where $\beta_M=$ `Mdata.betaM`, $\tau_1\psi=$ `Mdata.tau1 Mdata.psi`.
--
--   In (14.11.2) the character $\chi$ is $\psi^{\tau_1}$ or $-\bar\psi^{\tau_1}$; this public statement keeps only the pointwise norm consequence $|\chi|=|\psi^{\tau_1}|$.
--
--   **Formalization Note.** The proof derives the full classification internally; the stated conclusion records only the consequence about absolute values.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean#L1272-L1304

import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem betaM_expansion [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp)
    (hne : Mdata.K ≠ hyp.base.V) :
    Mdata.e = hyp.base.p * hyp.base.q ∧
      ∃ ε : Fin hyp.base.q → Fin hyp.base.p → ℤ,
        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        ∃ χ : ClassFunction G ℂ,
          (∀ g : G, ‖χ g‖ = ‖(Mdata.tau1 Mdata.psi) g‖) ∧
          Mdata.betaM =
            (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p,
              (ε i j : ℂ) • hyp.base.eta i j) - χ := by sorry

end OddOrder.Peterfalvi.S16
