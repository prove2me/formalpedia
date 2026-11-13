-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_etaGrid_projection_pythagorean
-- name    : OddOrder.Peterfalvi.S16.etaGrid_projection_pythagorean
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:08:30.295627+00:00
-- url     : https://prove2.me/theorems/07a002e6-655e-4499-92e3-984f2f9bb355
-- title:
--   Pythagoras for the $\eta$-grid: $\|\phi\|^2=\sum m_{ij}^2+\|\phi-\mathrm{proj}\|^2$
-- statement:
--   Let $G$ be a finite group and `hyp` a Peterfalvi §13 configuration with primes $p,q$ and orthonormal grid characters $\eta_{ij}$ ($i<q$, $j<p$). Let $\phi$ be a complex class function on $G$ and $m : \{0..q-1\}\times\{0..p-1\}\to\mathbb{Z}$ integers with $\langle\phi,\eta_{ij}\rangle = m_{ij}$ for all $i,j$. Then, with $X = \texttt{etaGridProjection hyp m}$ the class function $\sum m_{ij}\eta_{ij}$ built from the coefficients $m$,
--   $$\langle \phi,\phi\rangle \;=\; \sum_{i<q}\sum_{j<p} m_{ij}^2 \;+\; \langle \phi - X,\ \phi - X\rangle .$$
--
--   That is, the squared norm of $\phi$ is the sum of the squared Fourier coefficients on the orthonormal $\eta$-grid plus the squared norm of the perpendicular residual.
--
--   **Formalization Note.** The integer sum is cast to $\mathbb{C}$ as a whole. `etaGridProjection hyp m` is a project definition.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/CoherentProjectionRigidity.lean#L46-L109

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

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem etaGrid_projection_pythagorean [Finite G]
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (phi : ClassFunction G ℂ) (m : Fin hyp.q → Fin hyp.p → ℤ)
    (hcoeff : ∀ i j, ClassFunction.inner phi (hyp.eta i j) = (m i j : ℂ)) :
    ClassFunction.inner phi phi =
      ((∑ i : Fin hyp.q, ∑ j : Fin hyp.p, (m i j) ^ 2 : ℤ) : ℂ) +
        ClassFunction.inner (phi - etaGridProjection hyp m)
          (phi - etaGridProjection hyp m) := by sorry

end OddOrder.Peterfalvi.S16
