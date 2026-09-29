-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue
-- name    : LanglandsTunnell.CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2d1d5094-f848-5f2f-b199-168e98ed7f2c
-- title:
--   Window-truncated Jacquet integrals converge to the Jacquet value
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, i.e. a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, with completion $\mathbb{Q}_v$. Let $\nu_0,\nu_1,\nu_2$ be characters $\mathbb{Q}_v^\times \to \mathbb{C}^\times$, each locally constant, let $\Phi : \mathbb{Q}_v^3 \to \mathbb{C}$ be locally constant with compact support, and let $\chi$ be a locally constant character of $\mathbb{Q}_v^\times$ such that $\|(\nu_i\chi)(\varpi_v)\| = 1$ for each $i$, where $\varpi_v$ is the chosen uniformiser unit [`NumberField.AdelicLevel.uniformizerUnit`](def/NumberField_AdelicLevel.html#L788). Let $s \in \mathbb{C}$. Write $f =$ `cellSectionOf v ν Φ` for the function on $\mathrm{GL}_3(\mathbb{Q}_v)$ supported on the big cell $\{g : \mathrm{cornerEntry}(g) \neq 0,\ \mathrm{lowerMinor}(g) \neq 0\}$ and given there by `cellValue v ν g` times $\Phi(\mathrm{cellRatio}(g))$, and for a unit $a$ and $x \in \mathbb{Q}_v$ put $g_{a,x} = w_0 \cdot {}^{t}\!\big(\iota(\mathrm{diag}(a,1))\, u_{21}(x)\, (w' \cdot {}^{t}1^{-1})\big)^{-1} \cdot w_v$, with $w_0 =$ `longWeyl3`, $w' =$ `weylPrime3`, $w_v =$ `antidiagonal3`, $\iota$ the upper-left embedding of $\mathrm{GL}_2$ and $u_{21}(x)$ the lower unipotent matrix with $(2,1)$-entry $x$, and ${}^{t}(\cdot)^{-1}$ the transpose-inverse. Assume $K : \mathbb{Z} \to \mathbb{Q}_v \to \mathbb{Q}_v \to \mathbb{C}$ satisfies, for all $c \in \mathbb{Z}$, units $a$ and all $x$, $$K(c,a,x) = \int \psi_v(-(\alpha+\beta))\, f\big(w_v\, n(\alpha,\beta,\gamma)\, g_{a,x}\big)\, d\mu^{\otimes 3},$$ the integral being over the set of triples $(\alpha,\beta,\gamma)$ with $|\beta| \le q^{c}$, $|\gamma| \le q^{c}|\beta|$ and $|\alpha - \gamma/\beta| \le q^{c}$ against the triple product of the self-dual Haar measure, $\psi_v$ the standard local additive character and $n(\alpha,\beta,\gamma) =$ `upperUnipotent3`; and assume $J : \mathbb{Q}_v \to \mathbb{Q}_v \to \mathbb{C}$ satisfies $J(a,x) =$ `jacquetValue` of the right translate of $f$ by $g_{a,x}$, i.e. the stabilised value of the truncated Jacquet integrals of that translate. Then for all natural numbers $N$ and $R$, as $c \to \infty$ in $\mathbb{Z}$ the quantity $$\int_{q^{-N} \le |a| \le q^{N}} |a|^{-1}\,\chi^{-1}(a)\,|a|^{1-s} \Big( \int_{|x| \le q^{R}} \big(K(c,a,x) - J(a,x)\big)\, d\mu(x)\Big)\, d^{\times}\!a$$ tends to $0$, where $|a|$ denotes `modulus`, characters are extended by $0$ at the origin via `charExt`, and $d^{\times}\!a$ is the measure `mulMeasure` obtained from the self-dual Haar measure on the complement of $0$ with density $|a|^{-1}$.
--
--   This is the local analytic step which lets the truncation level be sent to infinity inside the $\mathrm{GL}_3$ Jacquet (Whittaker) integral attached to a big-cell principal-series section, uniformly over a compact annulus in the torus variable and a ball in the unipotent variable. It is used by [`LanglandsTunnell.CubicInduction.tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue`](thm.html#LanglandsTunnell.CubicInduction.tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue) to identify the limit of the truncated local zeta integrals with the integral of the Jacquet value.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.tendsto_setIntegral_annulus_setIntegral_ball_jacquetWindow_sub_jacquetValue
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ)
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
    (J : v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hJ : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      J a x =
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
          (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
            (weylPrime3 * transposeInv3 1)) * antidiagonal3 v) (cellSectionOf v ν Φ)))
    (N R : ℕ) :
    letI := localBorel ℚ v
    Filter.Tendsto
      (fun c : ℤ =>
        ∫ a in {t : v.adicCompletion ℚ | WithZero.exp (-(N : ℤ)) ≤ Valued.v t ∧ Valued.v t ≤ WithZero.exp (N : ℤ)},
          ((modulus a : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ a * ((modulus a : ℝ) : ℂ) ^ (1 - s) *
            ∫ x in {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (R : ℤ)}, (K c a x - J a x)
              ∂(selfDualHaarAt ℚ v)
          ∂(mulMeasure (selfDualHaarAt ℚ v)))
      Filter.atTop (nhds 0) := by sorry
