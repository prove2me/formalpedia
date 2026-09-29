-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
-- name    : LanglandsTunnell.CubicInduction.setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b2c121f5-b9df-5054-8705-cbc00432fe45
-- title:
--   Torus integral of the box-truncated Jacquet integral unfolded
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), three quasi-characters $\nu_0,\nu_1,\nu_2 \colon (\mathbb{Q}_v)^\times \to \mathbb{C}^\times$ given as $\nu$ on $\mathrm{Fin}\,3$, a function $\Phi$ on $\mathbb{Q}_v^3$, a further quasi-character $\chi$, a complex number $s$, integers $c,c'$, and a function $J \colon \mathbb{Q}_v \to \mathbb{C}$. The hypothesis `hJ` requires that for every unit $a$ the value $J(a)$ be the integral, against the triple product of the self-dual Haar measure `selfDualHaarAt` over the box $\{v(x) \le \exp(c),\; v(y) \le \exp(c),\; v(z) \le \exp(2c')\}$, of $\psi(-(x+y))$ — $\psi$ the standard local additive character `psiLocal` — times `cellSectionOf v ν Φ` evaluated at $w_0\, n(x,y,z)\,(\iota(\mathrm{diag}(a,1))\,w_0)$, where $n(x,y,z)$ is the upper unitriangular matrix with entries $x$ at $(1,2)$, $y$ at $(2,3)$, $z$ at $(1,3)$, $w_0$ is the antidiagonal permutation matrix, $\iota$ is the block embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ with last diagonal entry $1$, and `cellSectionOf` is the function supported on the big cell $\{$corner entry $\neq 0$, lower minor $\neq 0\}$ equal there to `cellValue v ν` times $\Phi$ of the ratio vector $(g_{21}/\text{corner}, g_{22}/\text{corner}, \text{outer minor}/\text{lower minor})$. Further data: a measurable set $S \subseteq \mathbb{Q}_v$, integrability of the above box integrand for each unit $a$, integrability of $t \mapsto \psi_c(-t)\,(\nu_2\chi)(t)\,|t|^s$ for the multiplicative measure $d^\times t = |t|^{-1}\,dt$ on $\mathbb{Q}_v \setminus \{0\}$ (here $\psi_c(t)$ means $\psi(t)$ if $v(t) \le \exp(c)$ and $0$ otherwise, quasi-characters are extended by $0$ at $0$ via `charExt`, and $|\cdot|$ is `modulus`), and integrability for $d^\times r\, d^\times u$ of $(r,u) \mapsto (\nu_2\chi)^{-1}(u)\,|u|^{1-s}\,(\nu_1\chi)(r)\,|r|^s \int \Phi(u,r,w)\,(\nu_0\nu_1^{-1})(r-uw)\,|r-uw|^{-1}\,\psi_c\!\big(w/(r-uw)\big)\,dw$. The conclusion asserts $\int_S J(b)\,\|b\|^{-1}\chi(b)\,|b|^s\,d^\times b = \nu_0(-1)\nu_1(-1)\int\!\!\int \Big(\int \mathbf{1}_S(ru^{-1}t)\,\mathbf{1}_{\{v(u^{-1}t)\le \exp(2c')\}}\,\psi_c(-t)\,(\nu_2\chi)(t)\,|t|^s\,d^\times t\Big)\cdot\Big((\nu_2\chi)^{-1}(u)|u|^{1-s}(\nu_1\chi)(r)|r|^s\int \Phi(u,r,w)(\nu_0\nu_1^{-1})(r-uw)|r-uw|^{-1}\psi_c\!\big(w/(r-uw)\big)dw\Big)\,d^\times u\,d^\times r$, the iterated integral being taken with $r$ outermost, then $u$, then $t$.
--
--   This is the unfolding step in the local analysis of the $\mathrm{GL}_3$ Jacquet–Whittaker integral of a big-cell section: it rewrites the torus integral of the box-truncated Jacquet integral against $\chi|\cdot|^s$ as an iterated integral in which a truncated Tate local zeta integral in $t$ is coupled to a kernel in $(r,u)$. It feeds `tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue`, where the truncation parameters $c, c'$ are let grow so that the truncated factor converges to a local zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal
open LanglandsTunnell.CubicInduction

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem LanglandsTunnell.CubicInduction.setIntegral_tallBoxJacquet_div_norm_mul_charExt_mul_cpow_eq
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (c c' : ℤ)
    (J : v.adicCompletion ℚ → ℂ)
    (hJ : ∀ a : (v.adicCompletion ℚ)ˣ, J a =
      ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
          Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')},
        NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (iotaGL (diagUnitGL2 a) * antidiagonal3 v))
        ∂(jacquetHaar3 v))
    (S : Set (v.adicCompletion ℚ)) (hS : MeasurableSet S)
    (hint : ∀ a : (v.adicCompletion ℚ)ˣ, IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        NumberField.StandardAddChar.psiLocal ℚ v (-(p.1 + p.2.1)) *
          cellSectionOf v ν Φ
            (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 * (iotaGL (diagUnitGL2 a) * antidiagonal3 v)))
      {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
          Valued.v p.1 ≤ WithZero.exp c ∧ Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp (2 * c')}
      (jacquetHaar3 v))
    (hIg : Integrable
      (fun t : v.adicCompletion ℚ =>
        (if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0) *
          charExt (ν 2 * χ) t * ((modulus t : ℝ) : ℂ) ^ s)
      (mulMeasure (selfDualHaarAt ℚ v)))
    (hWI : Integrable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (charExt (ν 2 * χ)⁻¹ p.2 * ((modulus p.2 : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) p.1 *
            ((modulus p.1 : ℝ) : ℂ) ^ s) *
          ∫ w, Φ ![p.2, p.1, w] *
              (charExt (ν 0 * (ν 1)⁻¹) (p.1 - p.2 * w) * ((modulus (p.1 - p.2 * w) : ℝ) : ℂ)⁻¹) *
              (if Valued.v (w / (p.1 - p.2 * w)) ≤ WithZero.exp c then
                (NumberField.StandardAddChar.psiLocal ℚ v (w / (p.1 - p.2 * w)) : ℂ) else 0)
            ∂(selfDualHaarAt ℚ v))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v)))) :
    ∫ b in S, J b / (‖b‖ : ℂ) * charExt χ b * ((modulus b : ℝ) : ℂ) ^ s ∂(mulMeasure (selfDualHaarAt ℚ v)) =
      charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        ∫ r, ∫ u, (∫ t, S.indicator (fun _ => (1 : ℂ)) (r * u⁻¹ * t) *
              (if Valued.v (u⁻¹ * t) ≤ WithZero.exp (2 * c') then (1 : ℂ) else 0) *
              ((if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0) *
                charExt (ν 2 * χ) t * ((modulus t : ℝ) : ℂ) ^ s) ∂(mulMeasure (selfDualHaarAt ℚ v))) *
            ((charExt (ν 2 * χ)⁻¹ u * ((modulus u : ℝ) : ℂ) ^ (1 - s) * charExt (ν 1 * χ) r *
                ((modulus r : ℝ) : ℂ) ^ s) *
              ∫ w, Φ ![u, r, w] *
                  (charExt (ν 0 * (ν 1)⁻¹) (r - u * w) * ((modulus (r - u * w) : ℝ) : ℂ)⁻¹) *
                  (if Valued.v (w / (r - u * w)) ≤ WithZero.exp c then
                    (NumberField.StandardAddChar.psiLocal ℚ v (w / (r - u * w)) : ℂ) else 0)
                ∂(selfDualHaarAt ℚ v))
          ∂(mulMeasure (selfDualHaarAt ℚ v)) ∂(mulMeasure (selfDualHaarAt ℚ v)) := by sorry
