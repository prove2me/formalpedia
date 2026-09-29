-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_pt_eq_of_mem
-- name    : ModularCurve.ComplexPlaceDictionary.exists_pt_eq_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ab46c5e1-b383-50d3-8776-1970d4c684a2
-- title:
--   Every place where j is regular comes from H
-- statement:
--   Let $N\ge 1$ and let $F_N = \mathbb{Q}(q\text{-expansions})$ be the intermediate field [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305), the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions $\mathrm{qExpand}\,\mathbb{Q}\,d\,(j_q)$ for the nonzero divisors $d\mid N$; let $\mathbb{C}F_N =$ [`ModularCurve.laurentBaseChange ℂ F_N`](def/ModularCurve_LaurentCoeff.html#L103) be the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the image of $F_N$ under the coefficientwise map $\mathbb{Q}((q))\to\mathbb{C}((q))$. Let $D$ be a complex place dictionary at level $N$: data assigning to each $\tau\in\mathfrak H$ a place $D.\mathrm{pt}\,\tau$ of $\mathbb{C}F_N$ over $\mathbb{C}$ (a valuation subring containing $\mathbb{C}$, not all of $\mathbb{C}F_N$, and a principal ideal ring) and a positive integer $D.\mathrm{ramification}\,\tau$, such that $D.\mathrm{pt}$ is constant on $\Gamma_0(N)$-orbits, an element $x$ lies in the valuation ring of $D.\mathrm{pt}\,\tau$ exactly when $z\mapsto\|\mathrm{realize}\,N\,x\,z\|$ is bounded along the punctured neighbourhood filter of $\tau$, and for $x\ne 0$ the meromorphic order of the realisation at $\tau$ equals $D.\mathrm{ramification}\,\tau$ times $\mathrm{ord}_{D.\mathrm{pt}\,\tau}(x)$. Let $P$ be any place of $\mathbb{C}F_N$ over $\mathbb{C}$ whose valuation subring contains the element $j_q$ of $\mathbb{C}F_N$, i.e. the coefficientwise image of the $q$-expansion of $j$. Then $P = D.\mathrm{pt}\,\tau$ for some $\tau\in\mathfrak H$.
--
--   This is the surjectivity half of the classical identification of the non-cuspidal points of $X_0(N)=\Gamma_0(N)\backslash\mathfrak H^{*}$ with the places of $\mathbb{C}(X_0(N))=\mathbb{C}(j(q^d):d\mid N)$ over $\mathbb{C}$ at which $j$ is regular: places not lying over $j=\infty$ are accounted for by points of the upper half-plane. It is used in the divisor-theoretic work on $X_0(N)$, for instance in the computation of Hecke divisors of single points, in the principality criterion for divisors with Abel–Jacobi image in the period lattice, and in the hyperplane-section estimates for $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_exists_pt_eq_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane in
open scoped MatrixGroups in

theorem ModularCurve.ComplexPlaceDictionary.exists_pt_eq_of_mem {N : ℕ} [NeZero N]
    (D : ModularCurve.ComplexPlaceDictionary N)
    (P : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)))
    (hP : (⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
        ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
          (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ :
        ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∈
      P.toValuationSubring) :
    ∃ τ : ℍ, D.pt τ = P := by sorry
