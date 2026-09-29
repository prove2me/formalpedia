-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
-- name    : LanglandsTunnell.CubicInduction.integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/a6b3a289-af05-51fa-a082-2b8ef3b9f9ad
-- title:
--   Unfolding the weighted dual zeta integral on GL₃
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_v$ for the completion, and let $\nu_0,\nu_1,\nu_2$ and $\chi$ be locally constant homomorphisms $\mathbb{Q}_v^\times \to \mathbb{C}^\times$, and $\Phi$ a locally constant, compactly supported function on $\mathbb{Q}_v^3$; assume $|(\nu_i\chi)(\varpi_v)| = 1$ for each $i$, where $\varpi_v$ is `uniformizerUnit`, and let $s \in \mathbb{C}$ with $0 < \operatorname{Re} s < 1$. Let $K : \mathbb{Z} \to \mathbb{Q}_v \to \mathbb{Q}_v \to \mathbb{C}$ satisfy, for every integer $c$, every unit $a$ and every $x$, that $K(c,a,x)$ is the integral over $\{(\alpha,\beta,\gamma) : \mathrm{v}(\beta) \le \exp c,\ \mathrm{v}(\gamma) \le \exp c\cdot \mathrm{v}(\beta),\ \mathrm{v}(\alpha - \gamma/\beta) \le \exp c\}$, against the triple product `jacquetHaar3` of the self-dual Haar measure, of $\psi_v(-(\alpha+\beta))$ times the big-cell section `cellSectionOf v ν Φ` evaluated at $\mathrm{antidiag}\cdot u(\alpha,\beta,\gamma)\cdot\bigl(w_0\cdot {}^{t}(\,\iota(\mathrm{diag}(a,1))\,u_{21}(x)\,(w'\cdot{}^{t}1)\,)^{-1}\cdot\mathrm{antidiag}\bigr)$; here `cellSectionOf` vanishes off the big cell where `cornerEntry` and `lowerMinor` are nonzero and equals `cellValue v ν g * Φ (cellRatio v g)` there, and ${}^{t}(\cdot)$ denotes `transposeInv3`. Finally let $c$ be an integer and $\omega$ a function on $\mathbb{Q}_v\times\mathbb{Q}_v$ with measurable uncurrying and $\|\omega(a,x)\| \le B$ for all $a,x$. Then three things hold: the five-variable function
--   $$\psi_v^{(c)}(-t_0)(\nu_0\chi)^{-1}(t_0)|t_0|^{1-s}\cdot\psi_v^{(c)}(-t_1)(\nu_1\chi)^{-1}(t_1)|t_1|^{1-s}\cdot\Phi(u,w_1,w_2)(\nu_2\chi)^{-1}(u)|u|^{1-s}(\nu_1\chi)(w_1)|w_1|^{s}(\nu_0\nu_1^{-1})(w_1-uw_2)|w_1-uw_2|^{-1}\psi_v^{(c)}\!\bigl(w_2/(w_1-uw_2)\bigr)\cdot\omega\bigl(t_0(t_1u/w_1),\,t_1u/w_1-(w_1-uw_2)^{-1}\bigr)$$
--   is integrable for the product of four copies of the multiplicative measure $|t|^{-1}\,dt$ with the additive self-dual measure in the last variable (each character extended by zero at $0$ via `charExt`, $|\cdot|$ being `modulus`, and $\psi_v^{(c)}$ the standard character cut off to $\mathrm{v}(\cdot)\le\exp c$ and zero elsewhere); the function $(q_1,q_2)\mapsto \omega(q_1,q_2)\,|q_1|^{-1}\chi^{-1}(q_1)|q_1|^{1-s}K(c,q_1,q_2)$ is integrable for the product of the multiplicative measure and the self-dual measure; and the two integrals agree.
--
--   This is the unfolding step that rewrites the $\omega$-weighted dual zeta integral of the level-$c$ Jacquet window kernel $K$ on $GL_3(\mathbb{Q}_v)$ as a five-fold integral of two cut-off Gauss factors against the coupled principal-series integrand, together with the integrability needed for the change of variables. It is used in the subsequent estimates for the dual zeta remainder outside an annulus and in the decomposition of the local zeta integral of the primed dual into explicit pieces plus an annulus integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (c : ℤ) (ω : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hω :
      letI := localBorel ℚ v
      Measurable (Function.uncurry ω))
    (B : ℝ) (hB : ∀ a x, ‖ω a x‖ ≤ B) :
    letI := localBorel ℚ v
    Integrable
        (fun y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
            v.adicCompletion ℚ =>
          (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                  charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                  charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
              (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                  (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                  (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                  (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                    ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                  (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                    (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                  else 0)) *
            ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹))
        ((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) ∧
      Integrable
          (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ =>
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2))
          ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) ∧
        ∫ q : v.adicCompletion ℚ × v.adicCompletion ℚ,
            ω q.1 q.2 *
              (((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2)
            ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) =
          ∫ y : (v.adicCompletion ℚ × v.adicCompletion ℚ) × v.adicCompletion ℚ × v.adicCompletion ℚ ×
              v.adicCompletion ℚ,
            (if Valued.v (-y.1.1) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.1) : ℂ) else 0) *
                    charExt (ν 0 * χ)⁻¹ y.1.1 * ((modulus y.1.1 : ℝ) : ℂ) ^ (1 - s) *
                  ((if Valued.v (-y.1.2) ≤ WithZero.exp c then (psiLocal ℚ v (-y.1.2) : ℂ) else 0) *
                    charExt (ν 1 * χ)⁻¹ y.1.2 * ((modulus y.1.2 : ℝ) : ℂ) ^ (1 - s)) *
                (Φ ![y.2.1, y.2.2.1, y.2.2.2] *
                    (charExt (ν 2 * χ)⁻¹ y.2.1 * ((modulus y.2.1 : ℝ) : ℂ) ^ (1 - s)) *
                    (charExt (ν 1 * χ) y.2.2.1 * ((modulus y.2.2.1 : ℝ) : ℂ) ^ s) *
                    (charExt (ν 0 * (ν 1)⁻¹) (y.2.2.1 - y.2.1 * y.2.2.2) *
                      ((modulus (y.2.2.1 - y.2.1 * y.2.2.2) : ℝ) : ℂ)⁻¹) *
                    (if Valued.v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) ≤ WithZero.exp c then
                      (psiLocal ℚ v (y.2.2.2 / (y.2.2.1 - y.2.1 * y.2.2.2)) : ℂ)
                    else 0)) *
              ω (y.1.1 * (y.1.2 * y.2.1 / y.2.2.1)) (y.1.2 * y.2.1 / y.2.2.1 - (y.2.2.1 - y.2.1 * y.2.2.2)⁻¹)
            ∂((((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))).prod
              ((mulMeasure (selfDualHaarAt ℚ v)).prod
                ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))) := by sorry
