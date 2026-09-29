-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isLocalZeta31ConvergentAbove_dualWhittakerFn3_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.isLocalZeta31ConvergentAbove_dualWhittakerFn3_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b74ae105-13c1-518b-b8b3-230981117d0b
-- title:
--   Convergence of the dual GL₃ local zeta integral
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$ carried by its Borel $\sigma$-algebra. Let $\nu_0,\nu_1,\nu_2 \colon \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be monoid homomorphisms, each locally constant, let $\Phi \colon \mathbb{Q}_v^3 \to \mathbb{C}$ be locally constant with compact support, and let $\chi \colon \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be a locally constant homomorphism such that for each $i$ the value $(\nu_i\chi)(\varpi_v)$ at the uniformiser unit `uniformizerUnit` has complex absolute value $1$. Let $\sigma_1 > 0$. The assertion is that `IsLocalZeta31ConvergentAbove` holds above $\sigma_1$ for the following data: the multiplicative measure on $\mathbb{Q}_v^\times$ obtained by pulling back along $a \mapsto a$ the measure `mulMeasure` of the self-dual additive Haar measure `selfDualHaarAt ℚ v` (that is, the restriction of the latter to $\mathbb{Q}_v \setminus \{0\}$ with density $|x|_v^{-1}$), the additive measure `selfDualHaarAt ℚ v` on $\mathbb{Q}_v$, the function $W'(g) = W(w_{\mathrm{long}} \cdot {}^{t}g^{-1} \cdot w_v)$ where $W$ is the Jacquet–Whittaker function `jacquetWhittaker3 v ν Φ` of the cell section of $(\nu,\Phi)$, $w_{\mathrm{long}}$ is the antidiagonal permutation matrix `longWeyl3` and $w_v$ is `antidiagonal3 v`, the character $\chi^{-1}$, and the group element `weylPrime3 * transposeInv3 1`. Unfolded, this says: for every $s \in \mathbb{C}$ with $\mathrm{Re}\,s > \sigma_1$, the function $$(a,x) \in \mathbb{Q}_v^\times \times \mathbb{Q}_v \ \mapsto\ W'\!\left(\iota(\mathrm{diag}(a,1))\, u_{21}(x)\, w'\right)\,\chi^{-1}(a)\,|a|_v^{\,s-1}$$ is integrable for the product of the two measures, where $\iota$ is the upper-left embedding $GL_2 \hookrightarrow GL_3$, $u_{21}(x)$ the lower unipotent matrix with entry $x$ in position $(2,1)$, $w' =$ `weylPrime3 * transposeInv3 1`, and $|\cdot|_v$ is the normalised modulus.
--
--   This is the local absolute convergence, in a right half-plane, of the zeta integral attached to the $(3,1)$-type local functional equation for the dual (long-Weyl transposed-inverse) Jacquet–Whittaker function of a $GL_3$ cell section at a finite place. It is used by [`LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3`](thm.html#LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3), where the two local zeta integrals are compared and their Laurent behaviour recorded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isLocalZeta31ConvergentAbove_dualWhittakerFn3_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.isLocalZeta31ConvergentAbove_dualWhittakerFn3_of_norm_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hν : ∀ i, IsLocallyConstant (ν i))
    (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) {σ₁ : ℝ}
    (hσ₁ : 0 < σ₁) :
    letI := localBorel ℚ v
    IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      (selfDualHaarAt ℚ v) (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v))) χ⁻¹
      (weylPrime3 * transposeInv3 1) σ₁ := by sorry
