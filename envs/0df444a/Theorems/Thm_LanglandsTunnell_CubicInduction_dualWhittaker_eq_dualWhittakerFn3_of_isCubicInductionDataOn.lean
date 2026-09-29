-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/1fc348f9-0fe1-505f-89c5-a5fce41dab07
-- title:
--   Dual Whittaker function of cubic induction data
-- statement:
--   Let $K$ be a number field, regarded as an integral extension of $\mathbb{Q}$ at the level of rings of integers, let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ with values in $\mathbb{C}$, and let $\mu\colon \mathbb{A}_K^{\times}\to\mathbb{C}^{\times}$ be a character of the idele group of $K$. Let $D$ be a subset of $GL_2(\mathbb{A}_{\mathbb{Q}})$, let $U$ assign to each ideal of $\mathcal{O}_{\mathbb{Q}}$ a subgroup of $GL_2(\mathbb{A}_{\mathbb{Q}})$, and let $\mathrm{gen}$ assign to each finite place an element of $GL_2(\mathbb{A}_{\mathbb{Q}})$; these determine the carrier data `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, namely the Borel structures and adelic Haar measures on $GL_2(\mathbb{A}_{\mathbb{Q}})$ and on $\mathbb{A}_{\mathbb{Q}}$, the set $D$, the full central subgroup, $U$, $\mathrm{gen}$, and the additive Haar measure conditioned on the adelic box. Let $X$ consist of a function `X.form` on $GL_3(\mathbb{A}_{\mathbb{Q}})$, global, local and archimedean Whittaker functions, a central character and a function `X.dualWhittaker`. Assume `IsCubicInductionDataOn K … ψ μ {v | IsBadPlace K μ v} X`, i.e. the full list of cubic induction laws for $X$ relative to $\psi$, $\mu$ and the set of places $v$ that are ramified in $K$ or twist-ramified above $K$ for $\mu$ (automorphy under $GL_3(\mathbb{Q})$, the central character law with an idele class character, cuspidality along both maximal parabolics, the identification of `X.whittaker` with the $\psi$-Whittaker integral of `X.form` and its transformation law, the mirabolic Fourier expansion, local Whittaker laws and factorisation outside the bad set, sphericality with the coefficients induced from $\mu$, level invariance, local multiplicity one, moderate growth, $K$-finiteness, moment and half-plane bounds, together with the corresponding statements for `X.dualWhittaker` and the dual form; summarised here), and assume `X.form` continuous. Then `X.dualWhittaker` equals $g\mapsto$ `X.whittaker` $(w_3\,{}^t g^{-1})$, with $w_3$ the long Weyl element of $GL_3$.
--
--   This identifies the dual (contragredient) Whittaker function attached to cubic induction data, defined as the $\psi^{-1}$-Whittaker integral of the dual form, with the explicit transform $W(w_3\,{}^tg^{-1})$ of the Whittaker function itself. It is used in the derivation of the functional equation for the $GL_3\times GL_1$ global zeta integral from the local ones, in the structured-data form of the Langlands–Tunnell converse argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.dualWhittaker_eq_dualWhittakerFn3_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (_hcont : Continuous X.form) :
    X.dualWhittaker = dualWhittakerFn3 X.whittaker := by sorry
