-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_torusJacquetValueFn_eq_zero
-- name    : LanglandsTunnell.CubicInduction.eventually_threefold_twistedDifference_torusJacquetValueFn_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/6b1eb5e4-a6fa-5bda-8a41-a4bb6d8b5da5
-- title:
--   Threefold twisted differences of torus Jacquet values vanish near 0
-- statement:
--   Fix a nonzero prime $v$ of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$ and write $\varpi$ for `uniformizerUnit ℚ v` in $(\mathbb{Q}_v)^\times$. Let $\nu_0,\nu_1,\nu_2$ be locally constant characters $(\mathbb{Q}_v)^\times \to \mathbb{C}^\times$, let $\Phi$ on $(\mathbb{Q}_v)^3$ be locally constant with compact support, and let $D$ be an operator with $D\,\alpha\,f\,a = f(a) - \alpha f(a/\varpi)$ for all $\alpha \in \mathbb{C}$, all $f : \mathbb{Q}_v \to \mathbb{C}$ and all $a$. With $\mathbb{Q}_v$ given its Borel structure, let $F : \mathbb{Q}_v \to \mathbb{C}$ satisfy $F(0)=0$ and, for every unit $a$, $F(a) = |a|^{-1}\,$`jacquetValue` of the right translate by $\mathrm{diag}(a,1,1)\cdot w_3$ of the cell section `cellSectionOf v ν Φ`, where $w_3$ is the antidiagonal permutation matrix, the cell section is the indicator of the big cell times `cellValue v ν` $\cdot\,\Phi \circ$ `cellRatio`, the Jacquet value is the stabilised truncated unipotent integral against `psiLocal`, and $|\cdot|$ is the module `modulus`. Then two assertions hold. First, $D_{\nu_0(\varpi)}D_{\nu_1(\varpi)}D_{\nu_2(\varpi)}F$ vanishes on a neighbourhood of $0$. Second, for every locally constant character $\chi$ of $(\mathbb{Q}_v)^\times$ and every $c : \mathrm{Fin}\,3 \to \mathbb{C}$ with $c_i = \nu_i(\varpi)$ whenever $\nu_i\chi$ satisfies `HasConductorExponentAt ℚ v _ 0`, i.e. is trivial on `higherUnitsAt ℚ v 0` (the minimality clause being vacuous at $0$), and $c_i = 0$ otherwise, the function $$a \mapsto \frac{\int_{\{|w|=1\}} F(aw)\,\chi(w)\, d\mu^\times(w)}{\mu^\times(\{|w|=1\})},$$ with $\chi$ extended by $0$ at $0$ and $\mu^\times$ the multiplicative measure obtained from the self-dual additive Haar measure at $v$ by the density $|x|^{-1}$ off $0$, has $D_{c_0}D_{c_1}D_{c_2}$ vanishing on a neighbourhood of $0$.
--
--   This is the local recurrence, in cell coordinates, satisfied near the origin by the torus values of the Jacquet–Whittaker function attached to a cell section of a principal series of $\mathrm{GL}_3(\mathbb{Q}_v)$, both in raw form and after projection to a character of the unit group. It is used in the derivation of the Laurent expansion and functional equation of the associated local zeta integral, namely by [`LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3`](thm.html#LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eventually_threefold_twistedDifference_torusJacquetValueFn_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.eventually_threefold_twistedDifference_torusJacquetValueFn_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ)
    (hD : ∀ (α : ℂ) (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ),
      D α f a = f a - α * f (a / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ))) :
    letI := localBorel ℚ v
    ∀ F : v.adicCompletion ℚ → ℂ, F 0 = 0 →
      (∀ a : (v.adicCompletion ℚ)ˣ,
        F a = jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (iotaGL (diagUnitGL2 a) * antidiagonal3 v)
          (cellSectionOf v ν Φ)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹) →
      (∀ᶠ x in nhds (0 : v.adicCompletion ℚ),
          D ((ν 0) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)
            (D ((ν 1) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)
              (D ((ν 2) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ) F)) x = 0) ∧
        ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsLocallyConstant χ → ∀ c : Fin 3 → ℂ,
          (∀ i, HasConductorExponentAt ℚ v (ν i * χ) 0 →
            c i = ((ν i) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)) →
          (∀ i, ¬ HasConductorExponentAt ℚ v (ν i * χ) 0 → c i = 0) →
          ∀ᶠ x in nhds (0 : v.adicCompletion ℚ),
            D (c 0) (D (c 1) (D (c 2) (fun a =>
              (∫ w in {x : v.adicCompletion ℚ | Valued.v x = 1}, F (a * w) * charExt χ w
                  ∂(mulMeasure (selfDualHaarAt ℚ v))) /
                (((mulMeasure (selfDualHaarAt ℚ v)).real {x : v.adicCompletion ℚ | Valued.v x = 1} : ℝ) : ℂ)))) x =
              0 := by sorry
