-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue
-- name    : LanglandsTunnell.CubicInduction.tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/3e1f119f-728d-50c6-84f1-4b5e54a846ab
-- title:
--   Local zeta integral as limit of truncated coupled integrals
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and write $\mu =$ `selfDualHaarAt ℚ v` for the Haar measure on the completion $\mathbb{Q}_v$ normalised by the conductor exponent of the standard additive character `psiLocal ℚ v`, $|x| =$ `modulus x` for the module (the distributive Haar character) of $x$, and $d^{\times}x =$ `mulMeasure` $\mu$ for the measure $|x|^{-1}\,d\mu$ on $\mathbb{Q}_v \setminus \{0\}$; for a character $\eta : \mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$, `charExt` $\eta$ extends $\eta$ by $0$ at the origin, and `localZeta` $\mu\, f\, \eta\, s = \int f(x)\,\eta(x)\,|x|^{s}\,d^{\times}x$. Let $\nu_0,\nu_1,\nu_2$ be locally constant homomorphisms $\mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$, let $\Phi$ be a locally constant, compactly supported function on $\mathbb{Q}_v^{3}$, and let $T : \mathbb{Q}_v \to \mathbb{C}$ be a function satisfying, for every unit $a$, $T(a) = |a|^{-1}\cdot$ `jacquetValue` of the right translate by $\iota(\mathrm{diag}(a,1))\cdot w$ of the cell section `cellSectionOf v ν Φ`; here $\iota$ is the block embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ adding a final $1$, $w =$ `antidiagonal3 v` is the element of $\mathrm{GL}_3(\mathbb{Q}_v)$ with antidiagonal matrix $(0,0,1;0,1,0;1,0,0)$, right translation is $W \mapsto (h \mapsto W(hg))$, `cellSectionOf v ν Φ` is the indicator of `bigCell3 v` times $g \mapsto$ `cellValue v ν g` $\cdot\,\Phi($`cellRatio v g`$)$, and `jacquetValue v u` is `jacquetTruncated3 v` at the level `jacquetLevel v u` of $u$. Let $\chi$ be a further locally constant homomorphism $\mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$ such that $|(\nu_i\chi)(\varpi)| = 1$ for $i = 0,1,2$, $\varpi$ the uniformizer unit `uniformizerUnit ℚ v`, and let $s \in \mathbb{C}$ with $0 < \mathrm{Re}\,s < 1$, assuming $x \mapsto T(x)\chi(x)|x|^{s}$ is integrable for $d^{\times}x$. Then, as $c \to \infty$ along the integers, the product of $\nu_0(-1)\nu_1(-1)$, of the local zeta integral at $s$ against $\nu_2\chi$ of the truncated character $t \mapsto \psi(-t)$ if $v(-t) \le q^{c}$ and $0$ otherwise, and of the triple integral over $(x,y,z)$ of $$\Phi(x,y,z)\,(\nu_2\chi)^{-1}(x)|x|^{1-s}\,(\nu_1\chi)(y)|y|^{s}\,(\nu_0\nu_1^{-1})(y-xz)\,|y-xz|^{-1}\,\psi\!\left(\tfrac{z}{y-xz}\right)\mathbf{1}_{v(z/(y-xz)) \le q^{c}}$$ with respect to $d^{\times}x\,d^{\times}y\,d\mu(z)$, converges to `localZeta` $\mu\,T\,\chi\,s$.
--
--   This is the local unfolding identity at a finite place behind the cubic-induction (Jacquet-style) computation: the Tate zeta integral of the torus function of a Whittaker cell section is exhibited as the limit of truncated Gauss-type zeta integrals multiplied by a coupled triple integral over the unipotent variables. It is used in the proof of `localZetaDual31_one_sub_eq_mul_localZeta30_of_mem_strip`, where comparison of the two sides in the strip $0 < \mathrm{Re}\,s < 1$ yields the local functional equation relating the zeta integral at $s$ and its dual at $1-s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue.lean

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

theorem LanglandsTunnell.CubicInduction.tendsto_localZeta_truncChar_mul_coupled_localZeta_of_jacquetValue
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (T : v.adicCompletion ℚ → ℂ)
    (hT : ∀ a : (v.adicCompletion ℚ)ˣ, T a =
      jacquetValue v
          (gl3AmbientRightTranslate (R := ℂ) (iotaGL (diagUnitGL2 a) * antidiagonal3 v) (cellSectionOf v ν Φ)) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (hint : Integrable (fun x => T x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v))) :
    Filter.Tendsto
      (fun c : ℤ => charExt (ν 0) (-1) * charExt (ν 1) (-1) *
        localZeta (selfDualHaarAt ℚ v)
          (fun t => if Valued.v (-t) ≤ WithZero.exp c then (NumberField.StandardAddChar.psiLocal ℚ v (-t) : ℂ) else 0)
          (ν 2 * χ) s *
        ∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
          Φ ![p.1, p.2.1, p.2.2] *
            (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
            (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
            (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
              (NumberField.StandardAddChar.psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ) else 0)
        ∂((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))))
      Filter.atTop (nhds (localZeta (selfDualHaarAt ℚ v) T χ s)) := by sorry
