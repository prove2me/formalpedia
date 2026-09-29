-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference
-- name    : LanglandsTunnell.CubicInduction.exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/5a0ff677-5752-5b3d-a448-82f024872aa2
-- title:
--   Local zeta integral factors through three local L-factors
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_v$ for the $v$-adic completion, $\varpi$ for the chosen uniformizer unit `uniformizerUnit`, $q=N(v)$ for the absolute norm of $v$, and let $\mu^{\times}$ be the multiplicative measure attached to the self-dual additive Haar measure `selfDualHaarAt` (namely its restriction to $\mathbb{Q}_v\setminus\{0\}$ with density $\|x\|^{-1}$, since `modulus` agrees with the norm). Given three characters $\eta_0,\eta_1,\eta_2 : \mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$ with $|\eta_i(\varpi)|=1$, a locally constant character $\chi$, and scalars $c_i\in\mathbb{C}$ such that $c_i\,\chi(\varpi)=\eta_i(\varpi)$ whenever $\eta_i$ is trivial on the units of valuation $1$ (conductor exponent $0$) and $c_i=0$ otherwise; let $D$ be the operator $D_\alpha f(a)=f(a)-\alpha f(a/\varpi)$. Let $\varphi:\mathbb{Q}_v\to\mathbb{C}$ be locally constant away from $0$ and vanishing where $\|t\|$ exceeds some bound $B$, and assume that its $\chi$-average over the unit sphere, $a\mapsto \bigl(\int_{\|w\|=1}\varphi(aw)\chi(w)\,d\mu^{\times}\bigr)/\mu^{\times}(\{\|w\|=1\})$, is annihilated by $D_{c_0}D_{c_1}D_{c_2}$ on a neighbourhood of $0$. Then there is $P:\mathbb{C}\to\mathbb{C}$ of the form $P(s)=Q(q^{-s})\,q^{ms}$ for some $Q\in\mathbb{C}[X]$ and $m\in\mathbb{N}$ such that for every $s$ with $\mathrm{Re}\,s>0$ at which $x\mapsto\varphi(x)\chi(x)\|x\|^{s}$ is $\mu^{\times}$-integrable, the local zeta integral satisfies $Z(\varphi,\chi,s)=\bigl(\prod_{i}L_v(\eta_i,s)\bigr)P(s)$, where $L_v(\eta_i,s)=(1-\eta_i(\varpi)q^{-s})^{-1}$ if $\eta_i$ has conductor exponent $0$ and $1$ otherwise.
--
--   This is the local analogue of Tate's statement that the zeta integrals of a fixed space of test functions form a fractional ideal over the Laurent polynomial ring $\mathbb{C}[q^{s},q^{-s}]$: a difference-equation hypothesis near $0$ forces the zeta integral of $\varphi$ to be divisible by the product of the three unramified local $L$-factors, with Laurent-polynomial quotient. It feeds the local functional-equation computations of the cubic induction, being used in [`LanglandsTunnell.CubicInduction.exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one`](thm.html#LanglandsTunnell.CubicInduction.exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one) and in [`LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3`](thm.html#LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem
LanglandsTunnell.CubicInduction.exists_laurent_localZeta_eq_prod_localLFactorAt_mul_of_twistedDifference
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hu : ∀ i, ‖((η i) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ)‖ = 1)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (c : Fin 3 → ℂ)
    (hc₀ : ∀ i, HasConductorExponentAt ℚ v (η i) 0 →
      c i * (χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ) =
        ((η i) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂ))
    (hc₁ : ∀ i, ¬ HasConductorExponentAt ℚ v (η i) 0 → c i = 0)
    (D : ℂ → (v.adicCompletion ℚ → ℂ) → v.adicCompletion ℚ → ℂ)
    (hD : ∀ (α : ℂ) (f : v.adicCompletion ℚ → ℂ) (a : v.adicCompletion ℚ),
      D α f a = f a - α * f (a / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ)))
    (φ : v.adicCompletion ℚ → ℂ) (hφ : ∀ t : v.adicCompletion ℚ, t ≠ 0 → ∀ᶠ t' in nhds t, φ t' = φ t)
    (hφB : ∃ B : ℝ, ∀ t : v.adicCompletion ℚ, B < (modulus t : ℝ) → φ t = 0)
    (hrec : ∀ᶠ x in nhds (0 : v.adicCompletion ℚ),
      D (c 0) (D (c 1) (D (c 2) (fun a =>
        (∫ w in {x : v.adicCompletion ℚ | Valued.v x = 1}, φ (a * w) * charExt χ w
            ∂(mulMeasure (selfDualHaarAt ℚ v))) /
          (((mulMeasure (selfDualHaarAt ℚ v)).real {x : v.adicCompletion ℚ | Valued.v x = 1} : ℝ) : ℂ)))) x = 0) :
    ∃ P : ℂ → ℂ,
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      ∀ s : ℂ, 0 < s.re →
        Integrable (fun x => φ x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s) (mulMeasure (selfDualHaarAt ℚ v)) →
          localZeta (selfDualHaarAt ℚ v) φ χ s = (∏ i, localLFactorAt ℚ v (η i) s) * P s := by sorry
