-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand
-- name    : LanglandsTunnell.CubicInduction.integrable_coupledIntegrand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/247bf6f3-12e8-50c4-9cff-01b713909e3f
-- title:
--   Integrability of the coupled cubic-induction integrand on 0<Re s<1
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and write $\mathbb{Q}_v$ for `v.adicCompletion ℚ`. Let $\nu_0,\nu_1,\nu_2\colon \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be monoid homomorphisms, each locally constant; let $\Phi\colon \mathbb{Q}_v^3 \to \mathbb{C}$ be locally constant with compact support; let $\chi\colon \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be a locally constant monoid homomorphism such that for each $i$ the complex number $(\nu_i\chi)(\varpi_v)$ has absolute value $1$, where $\varpi_v$ is the unit of $\mathbb{Q}_v$ given by the image of the chosen uniformizer of $v$; let $s \in \mathbb{C}$ with $0 < \mathrm{Re}\,s$ and $\mathrm{Re}\,s < 1$, and let $c \in \mathbb{Z}$. Writing $|a| =$ `modulus a` (the module of the unit $a$ for the additive Haar measure, and $0$ for $a=0$; it equals $\|a\|$ on $\mathbb{Q}_v$), and extending each character by $0$ at $0$ via `charExt`, the assertion is that $$(x,y,w)\mapsto \Phi(x,y,w)\,(\nu_2\chi)^{-1}(x)|x|^{1-s}\,(\nu_1\chi)(y)|y|^{s}\,(\nu_0\nu_1^{-1})(y-xw)|y-xw|^{-1}\,\psi_c\!\left(\tfrac{w}{y-xw}\right)$$ is integrable, where $\psi_c(t)$ is the value at $t$ of the standard local additive character `psiLocal` of $\mathbb{Q}_v$ when $v(t) \le \exp(c)$ and $0$ otherwise. The measure is the product, in this order, of `mulMeasure (selfDualHaarAt ℚ v)` in $x$, the same in $y$, and `selfDualHaarAt ℚ v` itself in $w$; here `selfDualHaarAt ℚ v` is the additive Haar measure on $\mathbb{Q}_v$ scaled by $N(v)^{-n/2}$ with $n$ the level of `psiLocal`, and `mulMeasure` is its restriction to $\mathbb{Q}_v \setminus \{0\}$ with density $|x|^{-1}$.
--
--   This is the convergence input for a Tate-style local computation in the cubic induction: the integrand couples two local zeta factors in $x$ and $y$ with a truncated additive character in the variable $w$, and the singularity along $y = xw$ is integrable precisely because $w$ carries the additive rather than the multiplicative measure. It is used in the unfolding of the integral of a weight against a Jacquet window and in the limit computation expressing a coupled local zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_coupledIntegrand.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open IsDedekindDomain
open NumberField
open LanglandsTunnell.TateLocal

attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem LanglandsTunnell.CubicInduction.integrable_coupledIntegrand
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) (c : ℤ) :
    Integrable
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        Φ ![p.1, p.2.1, p.2.2] *
          (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
          (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
          (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) * ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
          (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
            (NumberField.StandardAddChar.psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ) else 0))
      ((mulMeasure (selfDualHaarAt ℚ v)).prod ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v))) := by sorry
