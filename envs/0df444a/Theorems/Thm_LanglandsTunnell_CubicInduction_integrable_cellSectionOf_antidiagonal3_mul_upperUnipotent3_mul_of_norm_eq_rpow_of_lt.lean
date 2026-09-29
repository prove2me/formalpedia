-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt
-- name    : LanglandsTunnell.CubicInduction.integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/506f3f2f-9b29-5fdb-91f0-4282f34ea44b
-- title:
--   Absolute convergence of Jacquet integrals of GL₃ cell sections
-- statement:
--   Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, with completion $F = \mathbb{Q}_v$ carried with its Borel $\sigma$-algebra `localBorel`. Let $\nu_0,\nu_1,\nu_2 \colon F^{\times} \to \mathbb{C}^{\times}$ be group homomorphisms, each locally constant, and let $\sigma_0,\sigma_1,\sigma_2 \in \mathbb{R}$ be such that $\|\nu_i(x)\| = \|x\|^{\sigma_i}$ for all $x \in F^{\times}$ and all $i$; assume $\sigma_1 < \sigma_0$ and $\sigma_2 < \sigma_1$. Let $\Phi \colon F^3 \to \mathbb{C}$ be locally constant with compact support, and let $g \in \mathrm{GL}_3(F)$ be arbitrary. The assertion is that the function $$(x,y,z) \longmapsto (\mathrm{cellSectionOf}\ v\ \nu\ \Phi)\bigl(w_0 \cdot n(x,y,z) \cdot g\bigr)$$ is integrable on $F \times F \times F$ for `jacquetHaar3 v`, the threefold product of the self-dual Haar measure `selfDualHaarAt ℚ v` of $F$. Here $w_0 =$ `antidiagonal3 v` is the antidiagonal permutation matrix in $\mathrm{GL}_3(F)$, $n(x,y,z) =$ `upperUnipotent3 x y z` is the upper unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the upper right corner, and `cellSectionOf v ν Φ` is the function on $\mathrm{GL}_3(F)$ supported on the set `bigCell3 v` where `cornerEntry v h` and `lowerMinor v h` are both nonzero, and given there by $\mathrm{charExt}(\nu_0)(\det h / \mathrm{lowerMinor}\,h) \cdot \mathrm{charExt}(\nu_1)(\mathrm{lowerMinor}\,h / \mathrm{cornerEntry}\,h) \cdot \mathrm{charExt}(\nu_2)(\mathrm{cornerEntry}\,h) \cdot \bigl(\|\det h / \mathrm{lowerMinor}\,h\| / \|\mathrm{cornerEntry}\,h\|\bigr)$ times $\Phi$ evaluated at `cellRatio v h`, the triple of ratios built from the entries and minors of $h$.
--
--   This is the absolute-convergence statement underlying the representation of the Jacquet–Whittaker function of a cell section of the principal series $I(\nu)$ of $\mathrm{GL}_3(F)$ as an untruncated Jacquet integral over the unipotent radical, valid for every right translate of the section once the exponents lie in the chamber $\sigma_0 > \sigma_1 > \sigma_2$ (a rank-two instance of the Gindikin–Karpelevich convergence criterion). It is used by [`LanglandsTunnell.CubicInduction.integrable_and_jacquetWhittaker3_eq_integral_of_norm_eq_rpow_of_lt`](thm.html#LanglandsTunnell.CubicInduction.integrable_and_jacquetWhittaker3_eq_integral_of_norm_eq_rpow_of_lt), which pairs it with the identification of the integral with the Whittaker functional.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.integrable_cellSectionOf_antidiagonal3_mul_upperUnipotent3_mul_of_norm_eq_rpow_of_lt
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((ν i x : ℂˣ) : ℂ)‖ = ‖(x : v.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    Integrable (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      cellSectionOf v ν Φ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * g)) (jacquetHaar3 v) := by sorry
