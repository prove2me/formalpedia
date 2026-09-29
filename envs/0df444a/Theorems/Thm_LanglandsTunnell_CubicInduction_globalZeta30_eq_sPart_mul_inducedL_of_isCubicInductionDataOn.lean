-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/0ce69356-d4d7-5826-97cc-0fcce166e7e4
-- title:
--   Euler factorisation of the GL₃ zeta integral outside S
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ that is trivial on $\mathbb{Q}$, continuous and non-trivial, and let $\mu$ be a character of the ideles of $K$ that is trivial on principal ideles, continuous and unitary. Assume that at every finite place $v$ of $\mathbb{Q}$ which is not bad for $(K,\mu)$ — bad meaning ramified in $K$ or carrying a prime of $K$ above it at which $\mu$ is ramified — the local character `psiLoc` $\psi$ at $v$ has `addCharLevel` $0$. Let $D$, $U$ and $gen$ assemble, together with the adelic box, into the carrier pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)` (Borel structures, adelic Haar measure on $GL_2$, full central subgroup, and the additive adelic Haar measure conditioned on the box). Let $X$ consist of a function `form` on $GL_3(\mathbb{A}_{\mathbb{Q}})$, a global Whittaker function, local Whittaker functions, an archimedean Whittaker function, a central character and a dual Whittaker function, satisfying `IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X`: left invariance of `form` under $GL_3(\mathbb{Q})$, transformation under the centre by the central character, which is an idele class character, cuspidality along both parabolic radicals, identification of `whittaker` with the $\psi$-Fourier coefficient `whittaker3` of `form` and of `dualWhittaker` with the $\psi^{-1}$-coefficient of the dual form, the $\psi$- and $\psi^{-1}$-Whittaker transformation laws, Fourier expansions over the mirabolic index, the local Whittaker laws, factorizability of `whittaker` into archimedean and local factors over any finite set containing the bad places outside which $g$ is maximal-compact, sphericity at good places with Hecke eigenvalues given by `inducedCoeff K μ`, invariance of the local Whittaker function under the congruence subgroup `congruenceK1` of exponent `inducedLevelAt K μ v` at good unramified places, local Whittaker multiplicity one, moderate growth, $K$-finiteness at infinity, and finiteness of the iota moments and Whittaker half-plane integrals for `form` and its dual. Assume moreover that `X.form` is non-zero and that at every non-bad $v$ with $\psi$ of level $0$ one has `X.whittakerLoc v 1 = 1` and `HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v)`; let $S$ be a finite set of finite places consisting exactly of the bad places, and assume that for every admissible twist $\tau$ of $\mathbb{Q}$ and every $g\in GL_3(\mathbb{A}_{\mathbb{Q}})$ there is $\sigma_0$ such that for $\mathrm{Re}\,s>\sigma_0$ the function $a\mapsto W_X(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,\|a\|^{s-1}$ is integrable for the $S$-part measure $\nu_S$ of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679). Then for every admissible twist $\tau$ of $\mathbb{Q}$ which is unramified at every $p\notin S$ and every $g$ whose component at each $w\notin S$ lies in `localMaximalCompact3`, there are $L:\mathbb{C}\to\mathbb{C}$ and $\sigma_0\in\mathbb{R}$ such that for $\mathrm{Re}\,s>\sigma_0$ the family of inverses of `inducedEulerPoly ℚ (inducedCoeff K μ)` at $p$ evaluated at $\lambda_\tau(p)\,N(p)^{-s}$, over $p\notin S$, has product $L(s)$, and `globalZeta30 X.whittaker τ s g` equals the constant $c$ of the product measure data (namely $1$) times the $\nu_S$-integral of $W_X(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,\|a\|^{s-1}$ times $L(s)$.
--
--   This is the unramified Euler factorisation of the $GL_3$ Hecke–Jacquet zeta integral attached to cubic induction data: the global integral over the ideles of $\mathbb{Q}$ is split into an integral over the $S$-part and the partial induced $L$-function of the twist, whose local factors are the reciprocals of the degree-three induced Euler polynomials of $(K,\mu)$ twisted by $\tau$. It is the structured-data form of the factorisation used in the converse-theorem analysis, and feeds the identifications of the functional equation of the twisted zeta integrals in terms of local root numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.globalZeta30_eq_sPart_mul_inducedL_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS) :
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → IsUnramifiedCharAt τ p) → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
        componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
      ∃ (L : ℂ → ℂ) (σ₀ : ℝ), ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
            ((inducedEulerPoly ℚ (inducedCoeff K μ) p.1).eval
              (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p.1 * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)))⁻¹)
          (L s) ∧
        globalZeta30 X.whittaker τ s g =
          ((NumberField.Idele.productMeasureData ℚ S).c : ℂ) *
            (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
              X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) *
                ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.productMeasureData ℚ S).νS) *
            L s := by sorry
