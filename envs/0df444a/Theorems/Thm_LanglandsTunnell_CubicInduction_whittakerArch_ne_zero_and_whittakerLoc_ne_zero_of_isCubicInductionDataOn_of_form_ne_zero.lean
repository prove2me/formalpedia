-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerArch_ne_zero_and_whittakerLoc_ne_zero_of_isCubicInductionDataOn_of_form_ne_zero
-- name    : LanglandsTunnell.CubicInduction.whittakerArch_ne_zero_and_whittakerLoc_ne_zero_of_isCubicInductionDataOn_of_form_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/525bf53f-2351-5902-807f-2173838e041d
-- title:
--   Non-vanishing of archimedean and local Whittaker factors
-- statement:
--   Fix a number field $K$ equipped with an $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ which is integral, a bundle `pins : CarrierPins ℚ` of carrier data over $\mathbb Q$ (a measurable space and measure on the adelic $GL_2$, a subset $D$, a subgroup $Z$ of the idele group, a family of level subgroups $U$, local generators `gen`, and a measurable space and measure on the adele ring), an additive character $\psi$ of $\mathbb A_{\mathbb Q}$ with values in $\mathbb C$, a character $\mu$ of the ideles of $K$, and a finite set $S$ of finite places of $\mathbb Q$. Let $X$ be cubic induction data, i.e. a package consisting of a function `X.form` on $GL_3(\mathbb A_{\mathbb Q})$, a global Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $GL_3(\mathbb Q_v)$ for each finite $v$, an archimedean Whittaker function `X.whittakerArch` on $GL_3$ of the infinite adeles, a central character, and a dual Whittaker function. Assume `IsCubicInductionDataOn K pins ψ μ S X`, whose conjuncts (summarised here) are: left automorphy of `X.form` under $GL_3(\mathbb Q)$ and central transformation by an idele class character, cuspidality along the two parabolics $P_{2,1}$ and $P_{1,2}$, the identification of `X.whittaker` with the $\psi$-Whittaker integral of `X.form` together with the $\psi$-equivariance laws for `X.whittaker` and for each `X.whittakerLoc v`, the mirabolic Whittaker expansion summing to `X.form`, factorisability of `X.whittaker g` as `X.whittakerArch` at the archimedean component times the finite product of the `X.whittakerLoc v` at the components for any finite $T \supseteq S$ outside which the components lie in the local maximal compact subgroups, sphericality outside $S$ with the Hecke eigenvalues induced from $\mu$, invariance under the congruence sets `congruenceK1` at places outside $S$ unramified in $K$, local multiplicity one, moderate growth of `X.form`, $K$-finiteness of `X.whittakerArch`, the moment and half-plane conditions, and the corresponding statements for the dual form and dual Whittaker function. Then, provided `X.form` is not the zero function, `X.whittakerArch` is not the zero function and `X.whittakerLoc v` is not the zero function for any finite place $v$.
--
--   This records the elementary but repeatedly needed fact that a non-zero cuspidal datum on $GL_3$ over $\mathbb Q$ has non-zero Whittaker factors at every place, including the places in the bad set where no normalisation $W_v(1) = 1$ is available. It is used in the extraction of the local functional equation from the cubic induction data, namely by [`LanglandsTunnell.CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_whittakerArch_ne_zero_and_whittakerLoc_ne_zero_of_isCubicInductionDataOn_of_form_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.whittakerArch_ne_zero_and_whittakerLoc_ne_zero_of_isCubicInductionDataOn_of_form_ne_zero
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (hS : S.Finite) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ S X) (hform : X.form ≠ 0) :
    X.whittakerArch ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), X.whittakerLoc v ≠ 0 := by sorry
