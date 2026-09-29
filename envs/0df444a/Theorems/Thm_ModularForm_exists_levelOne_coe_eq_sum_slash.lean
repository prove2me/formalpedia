-- Prove2me | Theorems.Thm_ModularForm_exists_levelOne_coe_eq_sum_slash
-- name    : ModularForm.exists_levelOne_coe_eq_sum_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/df5dfc73-aeda-5197-bfd3-4a689dcb4749
-- title:
--   Trace of an even-weight modular form to level one
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, let $k$ be an even integer, and let $f$ be a modular form of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ (the subgroup of $\mathrm{GL}(\mathrm{Fin}\ 2,\mathbb{R})$ obtained by coercing $\Gamma$ along the natural map). Let $s$ be a finite subset of $\mathrm{SL}_2(\mathbb{Z})$ subject to two conditions: covering, that for every $g \in \mathrm{SL}_2(\mathbb{Z})$ there is $x \in s$ with $g x^{-1} \in \Gamma$ or $-(g x^{-1}) \in \Gamma$; and separation, that any $x, y \in s$ with $x y^{-1} \in \Gamma$ or $-(x y^{-1}) \in \Gamma$ are equal. Thus $s$ is a complete set of representatives for the right cosets of $\pm\Gamma$ in $\mathrm{SL}_2(\mathbb{Z})$ (finiteness of the index is not assumed, but follows). The conclusion asserts the existence of a modular form $F$ of weight $k$ for the full level-one group $\mathcal{SL}$, the image of $\mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{GL}_2(\mathbb{R})$, whose underlying function on the upper half-plane is literally the finite sum $\sum_{x \in s} f \mid_k x$ of weight-$k$ slash translates of $f$ by the images of the elements of $s$.
--
--   This is the trace map from weight-$k$ forms on $\Gamma$ to weight-$k$ forms on $\mathrm{SL}_2(\mathbb{Z})$, in even weight, computed over a prescribed set of coset representatives rather than an abstractly chosen one; keeping the representative set as an input allows it to be adapted to the cusps when Fourier coefficients of the trace are read off. It is used in the analysis of $q$-expansions of slashed forms, via [`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`](thm.html#ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_levelOne_coe_eq_sum_slash.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularForm.exists_levelOne_coe_eq_sum_slash
    (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (s : Finset SL(2, ℤ))
    (hcover : ∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) :
    ∃ F : ModularForm 𝒮ℒ k,
      (⇑F : UpperHalfPlane → ℂ) = ∑ x ∈ s, ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by sorry
