-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow
-- name    : LanglandsTunnell.CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/fcc51c63-48c1-5916-a351-3ee3fc528170
-- title:
--   Truncated Jacquet zeta integral factors through two Tate integrals
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ and write $\psi$ for the local component `psiLocal` of the standard adelic additive character, $\mu$ for the self-dual measure `selfDualHaarAt` (the additive Haar measure of the local integers scaled by $N(v)^{-n/2}$, $n$ the level of $\psi$), $|\cdot|$ for `modulus`, $\eta \mapsto$ `charExt`$\,\eta$ for the extension of a character of $\mathbb{Q}_v^{\times}$ to $\mathbb{Q}_v$ by $0$, and $Z(f,\eta,s)=\int f(x)\,\eta(x)\,|x|^{s}\,d^{\times}x$ for `localZeta`, the integral against $d^{\times}x=|x|^{-1}d\mu$ restricted to $x\neq 0$. Let $\nu_0,\nu_1,\nu_2$ be locally constant characters of $\mathbb{Q}_v^{\times}$, let $\Phi$ be locally constant with compact support on $\mathbb{Q}_v^{3}$, let $\chi$ be a locally constant character with $|(\nu_i\chi)(\varpi_v)|=1$ for all $i$, where $\varpi_v$ is `uniformizerUnit`, let $0<\Re s<1$, and let $c$ be an integer. Assume $K:\mathbb{Z}\to\mathbb{Q}_v\to\mathbb{Q}_v\to\mathbb{C}$ satisfies, for every integer $c$, every unit $a$ and every $x$, that $K(c,a,x)$ is the integral, against $\mu\otimes\mu\otimes\mu$ over the set of triples $(\alpha,\beta,\gamma)$ with valuations $\mathrm{val}(\beta)\le\exp c$, $\mathrm{val}(\gamma)\le\exp c\cdot\mathrm{val}(\beta)$ and $\mathrm{val}(\alpha-\gamma/\beta)\le\exp c$, of $\psi(-(\alpha+\beta))$ times the value of `cellSectionOf v ν Φ` at $$w\,u(\alpha,\beta,\gamma)\,\bigl(w_0\,\tau\bigl(\iota(\mathrm{diag}(a,1))\,n(x)\,(w'\,\tau(1))\bigr)\,w\bigr),$$ where $w=$`antidiagonal3`$\,v$ and $w_0=$`longWeyl3` are the antidiagonal permutation matrix, $w'=$`weylPrime3` interchanges the last two coordinates, $u(\alpha,\beta,\gamma)$ is the upper unipotent matrix with entries $\alpha,\beta,\gamma$, $n(x)$ is the lower unipotent matrix with $(2,1)$-entry $x$, $\iota$ embeds $\mathrm{GL}_2$ in the upper left corner, and $\tau(g)={}^{t}(g^{-1})$; here `cellSectionOf` is the function supported on the big cell $\{$`cornerEntry`$\,\neq 0$ and `lowerMinor`$\,\neq 0\}$ whose value there is `cellValue v ν g` $\cdot\,\Phi($`cellRatio v g`$)$, that is, $\nu_0$ of `gl3Det`$/$`lowerMinor` times $\nu_1$ of `lowerMinor`$/$`cornerEntry` times $\nu_2$ of `cornerEntry` times the real ratio $\|$`gl3Det`$/$`lowerMinor`$\|/\|$`cornerEntry`$\|$, evaluated on $\Phi$ at the triple of ratios $(g_{21}/$`cornerEntry`$, g_{22}/$`cornerEntry`$,$ `outerMinor`$/$`lowerMinor`$)$. Assume further that $F(c,a)=|a|^{-1}\int_{\mathbb{Q}_v}K(c,a,x)\,d\mu(x)$ for every integer $c$ and every unit $a$. Writing $\psi_c^{-}(t)=\psi(-t)$ if $\mathrm{val}(-t)\le\exp c$ and $0$ otherwise, the conclusion is $$Z(\psi_c^{-},(\nu_0\chi)^{-1},1-s)\;Z(\psi_c^{-},(\nu_1\chi)^{-1},1-s)\;I=Z(F(c,\cdot),\chi^{-1},1-s),$$ where $I$ is the integral against $d^{\times}x_1\,d^{\times}x_2\,d\mu(x_3)$ of $$\Phi(x_1,x_2,x_3)\,(\nu_2\chi)^{-1}(x_1)|x_1|^{1-s}\,(\nu_1\chi)(x_2)|x_2|^{s}\,(\nu_0\nu_1^{-1})(x_2-x_1x_3)\,|x_2-x_1x_3|^{-1}\,\Psi,$$ with $\Psi=\psi\bigl(x_3/(x_2-x_1x_3)\bigr)$ when $\mathrm{val}\bigl(x_3/(x_2-x_1x_3)\bigr)\le\exp c$ and $\Psi=0$ otherwise, all characters being extended by $0$ at $0$.
--
--   This is the local unfolding identity at a finite place in the $\mathrm{GL}_3$ strand of the cubic-induction argument: the Whittaker-type integral $F(c,\cdot)$ built from the big-cell section of the principal series, paired against $\chi^{-1}$ at $1-s$, factors as a product of two truncated Tate integrals in one variable and a single coupled three-variable integral of $\Phi$. It is used by `tendsto_localZeta_truncPsi_mul_coupled_of_forall_eq_integral_jacquetValue`, where the truncation level $c$ is let tend to infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow
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
    (F : ℤ → v.adicCompletion ℚ → ℂ)
    (hF : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ),
      letI := localBorel ℚ v
      F c a =
        (∫ x : v.adicCompletion ℚ, K c a x ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (c : ℤ) :
    letI := localBorel ℚ v
    localZeta (selfDualHaarAt ℚ v)
        (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 0 * χ)⁻¹ (1 - s) *
      localZeta (selfDualHaarAt ℚ v)
        (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 1 * χ)⁻¹ (1 - s) *
      (∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
          Φ ![p.1, p.2.1, p.2.2] *
            (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
            (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) *
              ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
            (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
              (psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ)
            else 0)
        ∂((mulMeasure (selfDualHaarAt ℚ v)).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) =
      localZeta (selfDualHaarAt ℚ v) (F c) χ⁻¹ (1 - s) := by sorry
