-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_isSlabDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/531a26ad-3513-5624-8109-47389da50f97
-- title:
--   Existence of slab fundamental domains in adelic GL₃/ℚ
-- statement:
--   Let $a,b$ be real numbers with $0<a$ and $a<b$. Write $\mathbb{A}$ for the adele ring of $\mathbb{Q}$ (the adele ring of the ring of integers of $\mathbb{Q}$ in $\mathbb{Q}$), and let $\mathrm{GL}_3(\mathbb{A})$ be `AdelicGL 3 (𝓞 ℚ) ℚ`, the group of units of $3\times 3$ matrices over $\mathbb{A}$. Let $\Gamma$ be the image of the monomorphism `globalPointsGL 3 (𝓞 ℚ) ℚ`, that is the subgroup of $\mathrm{GL}_3(\mathbb{A})$ consisting of the matrices coming from $\mathrm{GL}_3(\mathbb{Q})$ under the structure map $\mathbb{Q}\to\mathbb{A}$, and let `slabMeasure a b` be the adelic Haar measure [`NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ`](def/NumberField_AdelicHaar.html#L189) on $\mathrm{GL}_3(\mathbb{A})$ restricted to the set `ideleNormDetSlab a b`. The assertion is that there exists a subset $\Phi_0\subseteq \mathrm{GL}_3(\mathbb{A})$ satisfying `IsSlabDomain a b Φ₀`, i.e. such that $0<a$, $a<b$, and $\Phi_0$ is a fundamental domain in the measure-theoretic sense of Mathlib for the left translation action of $\Gamma$ on $\mathrm{GL}_3(\mathbb{A})$ with respect to `slabMeasure a b`: $\Phi_0$ is null measurable, almost every point has some $\Gamma$-translate lying in $\Phi_0$, and for distinct $\gamma_1\neq\gamma_2$ in $\Gamma$ the translates $\gamma_1\Phi_0$ and $\gamma_2\Phi_0$ are almost everywhere disjoint. The two inequalities on $a,b$ enter only as the first two conjuncts of `IsSlabDomain`; the fundamental domain produced by the proof exists for arbitrary real $a,b$.
--
--   This supplies the geometric substrate for the $L^2$ theory on determinant slabs in adelic $\mathrm{GL}_3$ over $\mathbb{Q}$: a fundamental domain for the rational points against which integrals of automorphic forms on the slab are computed. It is used in the estimates for smoothing operators and in the bounds on Whittaker integrals of cuspidal right-invariant functions that feed the cubic-induction step of Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_isSlabDomain (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsSlabDomain a b Φ₀ := by sorry
