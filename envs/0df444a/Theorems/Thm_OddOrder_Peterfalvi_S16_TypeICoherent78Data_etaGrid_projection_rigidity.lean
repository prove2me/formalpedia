-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_TypeICoherent78Data_etaGrid_projection_rigidity
-- name    : OddOrder.Peterfalvi.S16.TypeICoherent78Data.etaGrid_projection_rigidity
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:07:53.578624+00:00
-- url     : https://prove2.me/theorems/68a1bc10-552a-4ffc-b7fa-0cb829a1cd5f
-- title:
--   Peterfalvi (13.19.c): equality-case rigidity of the coherent $\eta$-projection
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, $L\le G$ a subgroup, `data : TypeICoherent78Data L`, and `hyp` a Peterfalvi §13 configuration with primes $p,q$ and grid $\eta_{ij}$. Put $\Phi = 1_G + \Gamma$, where $\Gamma$ is the residual $\Gamma$ of the (7.8.a) decomposition `data.betaDecomp hG`. Let $m_{ij}\in\mathbb{Z}$ ($i<q$, $j<p$) satisfy:
--
--   - $\langle \Phi,\eta_{ij}\rangle = m_{ij}$ for all $i,j$;
--   - principal value $m_{00}=1$;
--   - the (3.7) four-corner relation $m_{ij}+m_{00}=m_{i0}+m_{0j}$ for all $i,j$;
--   - $m_{0j}$ is odd for $j\ne0$, and $m_{i0}$ is odd for $i\neq 0$;
--   - the complement index $e$ of the (7.8) data satisfies $e\le pq$.
--
--   Then
--   $$e = pq,\qquad \forall i,j:\ m_{ij}=1\ \text{or}\ m_{ij}=-1,\qquad 1_G+\Gamma = \sum_{i,j} m_{ij}\,\eta_{ij},$$
--   where the last sum is `etaGridProjection hyp m`.
--
--   This packages the tight chain "lower bound $\le$ Bessel bound $\le e\le pq$" and is the rigidity step of (13.19.c). The orthogonality needed for the coefficient hypothesis is kept outside the theorem.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean#L169-L287

import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped BigOperators

variable {G : Type*} [Group G]

namespace TypeICoherent78Data

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem etaGrid_projection_rigidity [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (data : TypeICoherent78Data L)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hcoeff : ∀ i j,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma)
        (hyp.eta i j) = (m i j : ℂ))
    (hprincipal : m ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ = 1)
    (hrelation : ∀ i j,
      m i j + m ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ =
        m i ⟨0, hyp.p_prime.pos⟩ + m ⟨0, hyp.q_prime.pos⟩ j)
    (hrow : ∀ j, j ≠ ⟨0, hyp.p_prime.pos⟩ ->
      Odd (m ⟨0, hyp.q_prime.pos⟩ j))
    (hcol : ∀ i, i ≠ ⟨0, hyp.q_prime.pos⟩ ->
      Odd (m i ⟨0, hyp.p_prime.pos⟩))
    (he : (data.h78 hG).complementIndex ≤ hyp.p * hyp.q) :
    (data.h78 hG).complementIndex = hyp.p * hyp.q ∧
      (∀ i j, m i j = 1 ∨ m i j = -1) ∧
      OddOrder.Peterfalvi.S09.Hypothesis71.constOne G + (data.betaDecomp hG).Gamma =
        etaGridProjection hyp m := by sorry

end TypeICoherent78Data

end OddOrder.Peterfalvi.S16
