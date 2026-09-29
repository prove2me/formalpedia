-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_cellSectionOf_twistFamily_mul_eq
-- name    : LanglandsTunnell.CubicInduction.exists_isOpen_forall_cellSectionOf_twistFamily_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/a813549d-c80a-5fab-badd-0babe378f6d5
-- title:
--   Uniform right-invariance of cell sections along a twist family
-- statement:
--   Let $p$ be a point of the height-one spectrum of $\mathcal O_{\mathbb Q}$, and write $F_p$ for the completion `p.adicCompletion ℚ`. Let $\lambda = (\lambda_0,\lambda_1,\lambda_2)$ be a triple of monoid homomorphisms $F_p^\times \to \mathbb C^\times$, each locally constant, let $n = (n_0,n_1,n_2)$ be a triple of integers, and let $\lambda^{(\cdot)}$ be a family `lamU` assigning to each $u \in \mathbb C$ a triple of monoid homomorphisms $F_p^\times \to \mathbb C^\times$ whose values satisfy $\lambda^{(u)}_i(a) = \lambda_i(a)\,\lVert a\rVert^{n_i u}$ for all $u$, all $i$ and all $a \in F_p^\times$. Let $\Phi : F_p^3 \to \mathbb C$ be locally constant with compact support. The assertion is that there exists a subgroup $U$ of $\mathrm{GL}_3(F_p)$, open as a subset, such that for every $u \in \mathbb C$, every $k \in U$ and every $h \in \mathrm{GL}_3(F_p)$ one has $(\mathrm{cellSectionOf}\,p\,\lambda^{(u)}\,\Phi)(hk) = (\mathrm{cellSectionOf}\,p\,\lambda^{(u)}\,\Phi)(h)$; here `cellSectionOf` is the function supported on the big cell $\{g : \mathrm{cornerEntry}(g) \neq 0 \text{ and } \mathrm{lowerMinor}(g) \neq 0\}$ and given there by the product of $\mathrm{charExt}(\lambda^{(u)}_0)(\det g/\mathrm{lowerMinor}(g))$, $\mathrm{charExt}(\lambda^{(u)}_1)(\mathrm{lowerMinor}(g)/\mathrm{cornerEntry}(g))$, $\mathrm{charExt}(\lambda^{(u)}_2)(\mathrm{cornerEntry}(g))$, the real factor $\lVert \det g/\mathrm{lowerMinor}(g)\rVert/\lVert\mathrm{cornerEntry}(g)\rVert$, and $\Phi$ evaluated at the triple $(g_{21}/\mathrm{cornerEntry}(g),\, g_{22}/\mathrm{cornerEntry}(g),\, \mathrm{outerMinor}(g)/\mathrm{lowerMinor}(g))$. The point of the conclusion is that the single open subgroup $U$ works simultaneously for all members $\lambda^{(u)}$ of the twist family.
--
--   This is the statement that the big-cell sections of the degree-three principal series are smooth with a level that does not move as the inducing quasi-characters are twisted by the unramified family $\lVert\cdot\rVert^{n_i u}$. It is used in the analysis of the local Jacquet–Whittaker functions of the twist family and in the local Rankin–Selberg integral computation feeding the functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_cellSectionOf_twistFamily_mul_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

open scoped Classical

theorem LanglandsTunnell.CubicInduction.exists_isOpen_forall_cellSectionOf_twistFamily_mul_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    ∃ U : Subgroup (LocalGL3 p), IsOpen (U : Set (LocalGL3 p)) ∧
      ∀ (u : ℂ), ∀ k ∈ U, ∀ h : LocalGL3 p, cellSectionOf p (lamU u) Φ (h * k) = cellSectionOf p (lamU u) Φ h := by sorry
