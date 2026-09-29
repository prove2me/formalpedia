-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3
-- name    : LanglandsTunnell.CubicInduction.exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/19fe2305-3216-58ab-80a6-fb03c1f98c3d
-- title:
--   Invariant positive functional on the GL₃ principal series
-- statement:
--   Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_v$ for the $v$-adic completion of $\mathbb{Q}$, and let $\chi = (\chi_0,\chi_1,\chi_2)$ be a triple of group homomorphisms $\mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$. Assume that for every triple $a = (a_0,a_1,a_2)$ of units of $\mathbb{Q}_v$ one has $\prod_{i} \chi_i(a_i) = \lVert a_0\rVert/\lVert a_2\rVert$, i.e. the torus character attached to $\chi$ coincides with the half-modulus function. Then there is a $\mathbb{C}$-linear map $I$ on the submodule `principalSeries3 v χ` of functions $\varphi \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ that are locally constant, satisfy $\varphi(u g) = \varphi(g)$ for every upper triangular unipotent $u = \begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$, and satisfy $\varphi(\mathrm{diag}(a)g) = \bigl(\prod_i \chi_i(a_i)\bigr)\,\bigl(\lVert a_0\rVert/\lVert a_2\rVert\bigr)\,\varphi(g)$, with the following three properties: $I$ is invariant under right translation, $I(h \mapsto \varphi(hg)) = I(\varphi)$ for all $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ (the translate again lying in the submodule); $I(\varphi)$ is real whenever all values of $\varphi$ are real; and $\mathrm{Re}\,I(\varphi) > 0$ whenever $\varphi \neq 0$ and all values of $\varphi$ are real and non-negative.
--
--   This is the invariant integral over the flag variety for the principal series of $\mathrm{GL}_3$ over $\mathbb{Q}_v$ induced from the half-modulus character of the Borel subgroup, realised as a right-translation-invariant positive linear functional. It is used to construct a right-translation-invariant sesquilinear form on that principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hδ : ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ, torusChar3 v χ a = halfModulus3 v a) :
    ∃ I : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ,
      (∀ (g : LocalGL3 v) (φ : ↥(principalSeries3 v χ)),
        I ⟨gl3AmbientRightTranslate (R := ℂ) g φ, rightTranslate_mem_principalSeries3 φ.2 g⟩ = I φ) ∧
      (∀ φ : ↥(principalSeries3 v χ), (∀ g : LocalGL3 v, ((φ : LocalGL3 v → ℂ) g).im = 0) → (I φ).im = 0) ∧
      ∀ φ : ↥(principalSeries3 v χ),
        (∀ g : LocalGL3 v, 0 ≤ ((φ : LocalGL3 v → ℂ) g).re ∧ ((φ : LocalGL3 v → ℂ) g).im = 0) →
          φ ≠ 0 → 0 < (I φ).re := by sorry
