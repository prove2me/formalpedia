-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod
-- name    : LanglandsTunnell.CubicInduction.CubicInductionForm.dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ef2ba26d-d907-5d6a-b9e2-ec18760613a3
-- title:
--   Factorisation of the dual Whittaker function over a finite set
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral algebra over $\mathcal{O}_{\mathbb{Q}}$, let $\mathrm{pins}$ be a package of carrier data over $\mathbb{Q}$ (measurable structures, measures, a fundamental domain, a central subgroup, level subgroups and local generators for $\mathrm{GL}_2$ over the adeles), let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, and let $\mu$ be a character of the idele group of $K$. Let $D$ be a cubic induction form attached to $(K,\mathrm{pins},\psi,\mu)$, that is, a package consisting of a function $\mathrm{form}$ on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$, global, local and archimedean Whittaker functions, a central character and a dual Whittaker function, subject to the automorphy, central, cuspidality, Whittaker-expansion, factorisability, sphericality, level-invariance, multiplicity-one, growth and analytic conditions recorded in the structure. Assume $D.\mathrm{dualWhittaker}$ is the reflection $g \mapsto D.\mathrm{whittaker}(w_3 \cdot {}^{t}g^{-1})$ of its Whittaker function, where $w_3$ is the long Weyl element. Let $g$ be an adelic point of $\mathrm{GL}_3$ and $T$ a finite set of finite places of $\mathbb{Q}$ containing every $v$ that is bad for $(K,\mu)$, i.e. with $v$ ramified in $K$ or twist-ramified above $K$ for $\mu$, and such that for every $v \notin T$ the $v$-component of $g$ lies in the local maximal compact subgroup (all entries of the matrix and of its inverse of valuation at most $1$). Then $D.\mathrm{dualWhittaker}(g)$ equals the reflection of $D.\mathrm{whittakerArch}$ evaluated at the archimedean component of $g$, times the product over $v \in T$ of the reflections of the local Whittaker functions $D.\mathrm{whittakerLoc}\,v$ evaluated at the $v$-components of $g$.
--
--   This is the dual (reflected) counterpart of the finite factorisation of the Whittaker function of a cubic induction form on $\mathrm{GL}_3$: the factorisation over a finite set of places, carried across the involution $g \mapsto w_3\,{}^{t}g^{-1}$ which exchanges a Whittaker function with its dual. It is used in the Rankin–Selberg analysis of the induced form, in the construction of an entire, strip-bounded completed $L$-function attached to the Hecke datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_CubicInductionForm_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (D : CubicInductionForm K pins ψ μ) (hD1 : D.dualWhittaker = dualWhittakerFn3 D.whittaker)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v, IsBadPlace K μ v → v ∈ T)
    (hg : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    D.dualWhittaker g =
      dualWhittakerFn3 D.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
        ∏ v ∈ T, dualWhittakerFn3 (D.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v g) := by sorry
