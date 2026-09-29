-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero
-- name    : LanglandsTunnell.CubicInduction.eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/d7ec6a37-544c-5c86-a266-e9dc91151600
-- title:
--   Threefold twisted differences of dual Jacquet values vanish near 0
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), with $\mathbb{Q}_v=$ `v.adicCompletion ℚ` carrying its Borel $\sigma$-algebra, and write $\varpi$ for the uniformizer unit `uniformizerUnit ℚ v`. Let $\nu_0,\nu_1,\nu_2$ be locally constant homomorphisms $\mathbb{Q}_v^\times\to\mathbb{C}^\times$, let $\Phi:\mathbb{Q}_v^3\to\mathbb{C}$ be locally constant with compact support, and let $D$ be any operator with $D(\alpha)(f)(a)=f(a)-\alpha f(a/\varpi)$. For $a\in\mathbb{Q}_v^\times$ and $x\in\mathbb{Q}_v$ set $g(a,x)=w_3\cdot{}^{t}\!\big(\iota(\mathrm{diag}(a,1))\,u_{21}(x)\,(w'\cdot{}^{t}1^{-1})\big)^{-1}\cdot w_0$, built from the antidiagonal permutation `longWeyl3`, the transpose-inverse map, the lower unipotent with entry $x$ in position $(2,1)$, the permutation `weylPrime3`, and `antidiagonal3 v`; let $W(a,x)$ be `jacquetValue` (the stabilised truncated Whittaker integral) of the right translate by $g(a,x)$ of the cell section `cellSectionOf v ν Φ`, the function on $GL_3(\mathbb{Q}_v)$ supported on the big cell given there by the $\nu$-cocycle `cellValue` times $\Phi$ of the cell coordinates. Two assertions are made. First, for every $x$ and every $F$ with $F(0)=0$ and $F(a)=W(a,x)\,|a|^{-1}$ on units, $D(\nu_0(\varpi)^{-1})D(\nu_1(\varpi)^{-1})D(\nu_2(\varpi)^{-1})F$ vanishes on a neighbourhood of $0$. Second, for every locally constant character $\chi$ of $\mathbb{Q}_v^\times$ and every $c:\mathrm{Fin}\,3\to\mathbb{C}$ with $c_i\chi^{-1}(\varpi)=(\nu_i\chi)^{-1}(\varpi)$ whenever $(\nu_i\chi)^{-1}$ has conductor exponent $0$ at $v$ (trivial on the units of valuation $1$) and $c_i=0$ otherwise, and every $G$ with $G(0)=0$ and $G(a)=\big(\int_{\mathbb{Q}_v}W(a,x)\,dx\big)|a|^{-1}$ on units for the self-dual measure, the $\chi^{-1}$-projection $a\mapsto\big(\int_{|w|=1}G(aw)\chi^{-1}(w)\big)/\mathrm{vol}\{|w|=1\}$ for the multiplicative measure is annihilated near $0$ by $D(c_0)D(c_1)D(c_2)$. Here $|\cdot|$ is `modulus`, and $\chi^{-1}$ is extended by $0$ at $0$.
--
--   This is the local rationality input on the dual side of the $GL_3$ zeta integral: the germ at $0$ of the Jacquet–Whittaker slice, and of each of its character projections, satisfies a three-term twisted recurrence in the valuation, with twists given by the values of the inducing characters (respectively of the prescribed scalars $c_i$) at a uniformizer. It is used in the analysis of the dual local zeta integral at $v$, namely in the Laurent expansion of `localZetaDual31` and in the convergence statement for `dualWhittakerFn3` when the norm equals one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.eventually_threefold_twistedDifference_dualJacquetValueFn_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ)
    (hD : ∀ (α : ℂ) (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ),
      D α f a = f a - α * f (a / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ))) :
    letI := localBorel ℚ v
    (∀ x : v.adicCompletion ℚ, ∀ F : v.adicCompletion ℚ → ℂ, F 0 = 0 →
      (∀ a : (v.adicCompletion ℚ)ˣ,
        F a = jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
            (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
              antidiagonal3 v)
            (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
      ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
        D ((((ν 0) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ)
          (D ((((ν 1) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ)
            (D ((((ν 2) (NumberField.AdelicLevel.uniformizerUnit ℚ v))⁻¹ : ℂˣ) : ℂ) F)) t = 0) ∧
      ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsLocallyConstant χ → ∀ c : Fin 3 → ℂ,
        (∀ i, HasConductorExponentAt ℚ v (ν i * χ)⁻¹ 0 →
          c i * (χ⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ) =
            ((ν i * χ)⁻¹ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)) →
        (∀ i, ¬ HasConductorExponentAt ℚ v (ν i * χ)⁻¹ 0 → c i = 0) →
        ∀ G : v.adicCompletion ℚ → ℂ, G 0 = 0 →
          (∀ a : (v.adicCompletion ℚ)ˣ,
            G a = (∫ x : v.adicCompletion ℚ, jacquetValue v (gl3AmbientRightTranslate (R := ℂ)
                  (longWeyl3 *
                    transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 1)) *
                  antidiagonal3 v)
                (cellSectionOf v ν Φ)) ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
          ∀ᶠ t in nhds (0 : v.adicCompletion ℚ),
            D (c 0) (D (c 1) (D (c 2) (fun a =>
              (∫ w in {x : v.adicCompletion ℚ | Valued.v x = 1}, G (a * w) * charExt χ⁻¹ w
                  ∂(mulMeasure (selfDualHaarAt ℚ v))) /
                (((mulMeasure (selfDualHaarAt ℚ v)).real {x : v.adicCompletion ℚ | Valued.v x = 1} : ℝ) : ℂ)))) t =
              0 := by sorry
