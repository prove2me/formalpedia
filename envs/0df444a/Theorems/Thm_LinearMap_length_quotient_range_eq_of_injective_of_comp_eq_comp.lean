-- Prove2me | Theorems.Thm_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp
-- name    : LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e276df5c-f4d5-53ae-b583-97f124ab32c7
-- title:
--   Isogeny invariance of cokernel length over a DVR
-- statement:
--   Let $A$ be a commutative ring which is a domain and a discrete valuation ring, let $r$ be a natural number, and consider the free module $A^r$ in the form $\mathrm{Fin}\ r \to A$. Let $F_1$, $F_2$, $\varphi$ be $A$-linear endomorphisms of $A^r$ and assume that $F_1$ is injective, that $\varphi$ is injective, and that the square commutes in the form $\varphi \circ F_2 = F_1 \circ \varphi$ (written with `∘ₗ`, so that $F_2$ followed by $\varphi$ agrees with $\varphi$ followed by $F_1$). The conclusion is an equality of module lengths in $\mathbb{N} \cup \{\infty\}$, namely $$\mathrm{length}_A\bigl(A^r/\mathrm{im}\,F_1\bigr) = \mathrm{length}_A\bigl(A^r/\mathrm{im}\,F_2\bigr),$$ the lengths of the quotients of $A^r$ by the ranges of $F_1$ and of $F_2$ respectively. No injectivity of $F_2$ is assumed (it follows from the hypotheses), and no finiteness of either length is assumed; finiteness of the common value is part of what the proof establishes.
--
--   This is the isogeny invariance of the index $[M : FM]$ of a full-rank sublattice of a lattice over a discrete valuation ring: an intertwining injective map $\varphi$ from $(A^r, F_2)$ to $(A^r, F_1)$ forces the two cokernels to have the same length. It is used in the theory of Honda systems, at [`Deformation.HondaSystem.comap_L_eq_of_injective_of_map_L_le`](thm.html#Deformation.HondaSystem.comap_L_eq_of_injective_of_map_L_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {r : ℕ}
    (F₁ F₂ φ : (Fin r → A) →ₗ[A] (Fin r → A))
    (hF₁ : Function.Injective F₁) (hφ : Function.Injective φ)
    (hcomm : φ ∘ₗ F₂ = F₁ ∘ₗ φ) :
    Module.length A ((Fin r → A) ⧸ LinearMap.range F₁) =
      Module.length A ((Fin r → A) ⧸ LinearMap.range F₂) := by sorry
