-- Prove2me | Theorems.Thm_MvFormalGroup_mem_firstOrderCoboundaries_iff
-- name    : MvFormalGroup.mem_firstOrderCoboundaries_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/40a0ac9d-a783-56b0-9bf3-a090911ac7bb
-- title:
--   Explicit description of first-order deformation coboundaries
-- statement:
--   Let $k$ be a field, $d$ a natural number, and let $G_0$ be a $d$-dimensional formal group law over $k$: a $d$-tuple $G_{0,l}$ of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant terms, linear coefficients $\delta_{lj}$ in each of the two groups of variables, and satisfying the associativity identity; assume moreover that $G_0$ is commutative, i.e. interchanging the two groups of variables fixes each $G_{0,l}$. Let $b$ be a $d$-tuple of power series in the same $2d$ variables. The assertion is that $b$ belongs to `firstOrderCoboundaries G₀`, the $k$-span of the $\varepsilon$-parts (coefficientwise second components) of those deformations of $G_0$ over the dual numbers $k[\varepsilon]$ whose formal group law is commutative and which are isomorphic, in the sense of an invertible homomorphism of formal group laws reducing to the identity modulo $\varepsilon$, to a deformation with vanishing $\varepsilon$-part, if and only if there exists a $d$-tuple $\eta = (\eta_i)$ of power series in $d$ variables with $\mathrm{constantCoeff}(\eta_i) = 0$ such that for every $l$
--   $$b_l = \sum_i \eta_i(X)\,\partial_{X_i}G_{0,l} + \sum_i \eta_i(Y)\,\partial_{Y_i}G_{0,l} - \eta_l(G_0(X,Y)),$$
--   where $X$, $Y$ denote the two groups of variables, substitution is `MvPowerSeries.subst`, and $\partial$ is the coefficientwise formal partial derivative `pderivLin`.
--
--   This identifies the coboundary subspace in the first-order (tangent space) deformation theory of a commutative formal group law with the space of tuples obtained from strict automorphisms $X \mapsto X + \varepsilon\eta(X)$ of the trivial deformation. It is used in the comparison of isomorphism of deformations over the dual numbers with the corresponding shift of the $\varepsilon$-part, in [`MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy`](thm.html#MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy) and [`MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso`](thm.html#MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_mem_firstOrderCoboundaries_iff.lean

import Mathlib
import Definitions.Def_MvFormalGroup_FirstOrderDeformation
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries MvFormalGroup

theorem MvFormalGroup.mem_firstOrderCoboundaries_iff
    {k : Type} [Field k] {d : ℕ} (G₀ : MvFormalGroup d k) [G₀.IsComm]
    (b : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :
    b ∈ firstOrderCoboundaries G₀ ↔
      ∃ η : Fin d → MvPowerSeries (Fin d) k, (∀ i, constantCoeff (η i) = 0) ∧
        ∀ l, b l = ∑ i, subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) k)) (η i) * pderivLin (Sum.inl i) (G₀.toPowerSeries l)
                  + ∑ i, subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k)) (η i) * pderivLin (Sum.inr i) (G₀.toPowerSeries l)
                  - subst G₀.toPowerSeries (η l) := by sorry
