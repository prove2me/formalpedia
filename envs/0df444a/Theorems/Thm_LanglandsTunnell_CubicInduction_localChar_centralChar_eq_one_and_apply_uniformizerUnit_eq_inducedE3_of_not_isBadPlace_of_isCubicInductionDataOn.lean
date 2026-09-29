-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/7cb95d09-d278-5344-ae0d-f63f7cd70476
-- title:
--   Local central character at good places equals e₃
-- statement:
--   Let $K$ be a number field, $\psi$ an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, and $\mu$ a homomorphism from the idele units of $K$ to $\mathbb{C}^\times$; let `pins` be a package of measure-theoretic carrier data for $\mathbb{Q}$ (a measurable space and measure on $GL_2$ of the adeles, a region $D$, a central subgroup $Z$, level subgroups indexed by ideals, a prime-indexed family of group elements, and a measurable space and measure on the adeles), and let $X$ be cubic induction data, i.e. a form on $GL_3$ of the adeles of $\mathbb{Q}$ together with a global Whittaker function, local Whittaker functions at the finite places, an archimedean Whittaker function, a central character $\omega_X$ on the idele units, and a dual Whittaker function. Assume `IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X`, that is, the full list of laws tying these pieces together relative to the set of places $v$ that are bad for $(K,\mu)$ (ramified in $K$, or twist-ramified above): left invariance of the form under the rational points, transformation under central scalars by $\omega_X$, triviality of $\omega_X$ on principal ideles, cuspidality along the two maximal parabolics, agreement of the Whittaker function with the $\psi$-Whittaker integral of the form and the corresponding $\psi$-equivariance law, the Fourier expansion of the form over mirabolic cosets, the local $\psi_v$-equivariance laws, factorisation of the Whittaker function as the archimedean factor times a finite product of local factors over any finite set containing the bad places when the remaining components are integral, induced-sphericality with coefficients `inducedCoeff K μ` and invariance under the congruence subgroup of the induced level at the good, unramified places, local Whittaker multiplicity one, moderate growth, $K$-finiteness of the archimedean factor, the iota-moment and Whittaker half-plane conditions, and the corresponding statements for the dual form and dual Whittaker function (summarised here). Assume further that $X$'s form is not identically zero, that $T_0$ is a finite set of primes of $\mathbb{Q}$ containing every bad place of $(K,\mu)$, and that $v$ is a prime of $\mathbb{Q}$ which is not bad. Then the local component of $\omega_X$ at $v$ — the composite of $\omega_X$ with the embedding of $(\mathbb{Q}_v)^\times$ into the idele units at the coordinate $v$ — takes the value $1$ on every unit $u$ of $\mathbb{Q}_v$ with $\mathrm{v}(u)=1$, and its value at the distinguished uniformiser unit of $\mathbb{Q}_v$ equals $-$ the coefficient of degree $3$ of the induced Euler polynomial at $v$ formed from the coefficients $\mathfrak{P}\mapsto \mu(\varpi_{\mathfrak{P}})$ at the primes of $K$ where $\mu$ is unramified (and $0$ elsewhere).
--
--   This identifies the central character of a cubic induction datum at a place outside the bad set: it is unramified there and its value on a uniformiser is the degree-$3$ coefficient attached to the automorphic induction of $\mu$ from $K$ to $\mathbb{Q}$. It feeds the computation of the central character as a finite product in [`LanglandsTunnell.CubicInduction.exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn`](thm.html#LanglandsTunnell.CubicInduction.exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn), on the way to recognising the $GL_3$ form as the automorphic induction used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hF : X.form ≠ 0)
    (T₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT₀ : ∀ v, IsBadPlace K μ v → v ∈ T₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    (∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        localChar X.centralChar v u = 1) ∧
      ((localChar X.centralChar v (uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
        inducedE3 ℚ (inducedCoeff K μ) v := by sorry
