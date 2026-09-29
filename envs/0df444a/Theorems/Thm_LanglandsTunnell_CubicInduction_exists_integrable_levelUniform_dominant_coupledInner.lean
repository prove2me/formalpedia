-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_levelUniform_dominant_coupledInner
-- name    : LanglandsTunnell.CubicInduction.exists_integrable_levelUniform_dominant_coupledInner
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/19a6fcd5-e38b-5712-847e-f13f92e1fa6b
-- title:
--   Level-uniform integrable dominants for a cubic-induction inner integral
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and write $F_v$ for the completion $\mathbb{Q}_v$ with its valuation $\mathrm{Valued.v}$. Let $\nu_0,\nu_1,\nu_2$ be locally constant homomorphisms $F_v^{\times}\to\mathbb{C}^{\times}$, let $\chi$ be another such, assume $\|(\nu_i\chi)(\pi_v)\|=1$ for each $i$, where $\pi_v$ is the unit `uniformizerUnit` attached to the chosen uniformiser of $v$, let $\Phi:F_v^3\to\mathbb{C}$ be locally constant with compact support, and let $s\in\mathbb{C}$ satisfy $0<\operatorname{Re} s<1$. Write $|x|=\mathrm{modulus}\,x$ (the module of $x$ as a scaling factor of additive Haar measure, set to $0$ at $x=0$), extend quasi-characters by $0$ at $0$ via `charExt`, let $\mu_v$ be the self-dual additive Haar measure $\mathrm{selfDualHaarAt}$ on $F_v$ (the Haar measure giving $\mathcal{O}_v$ mass $1$, rescaled by $N(v)^{-\ell/2}$ with $\ell$ the level of the local component $\psi_v=\mathrm{psiLocal}$ of the standard adelic additive character), and let $d^\times$ be $\mathrm{mulMeasure}(\mu_v)$, namely $\mu_v$ restricted to $F_v\setminus\{0\}$ with density $|x|^{-1}$. For $c\in\mathbb{Z}$ and $t=(t_1,t_2)\in F_v\times F_v$ consider $$A_c(t)=(\nu_2\chi)^{-1}(t_1)|t_1|^{1-s}\,(\nu_1\chi)(t_2)|t_2|^{s}\int_{F_v}\Phi(t_1,t_2,w)\,(\nu_0\nu_1^{-1})(t_2-t_1w)\,|t_2-t_1w|^{-1}\,\psi_v\!\left(\tfrac{w}{t_2-t_1w}\right)\mathbf{1}\!\left[\mathrm{Valued.v}\!\left(\tfrac{w}{t_2-t_1w}\right)\le \exp(c)\right]d\mu_v(w),$$ and let $A_{c,m}(t)$ be the same expression with the $w$-integral restricted to $\{w: \mathrm{Valued.v}(t_2-t_1w)\le\exp(-m)\}$. The assertion is twofold: first, there is $D:F_v\times F_v\to\mathbb{R}$, integrable for $d^\times\!\otimes d^\times$, with $\|A_c(t)\|\le D(t)$ for all $c\in\mathbb{Z}$ and all $t$; second, there are $E_m:F_v\times F_v\to\mathbb{R}$ ($m\in\mathbb{N}$), each integrable for $d^\times\!\otimes d^\times$, with $\|A_{c,m}(t)\|\le E_m(t)$ for all $m$, $c$ and $t$, and with $\int E_m\,d^\times\!\otimes d^\times\to 0$ as $m\to\infty$.
--
--   This supplies the two analytic inputs — a single dominant valid uniformly in the truncation level $c$, and a family of dominants whose masses vanish on the shrinking regions $|t_2-t_1w|\le q^{-m}$ — needed to interchange limits in the local zeta integral arising from cubic induction on $\mathrm{GL}(3)$ over $\mathbb{Q}_v$. It is used in the estimates for the dual zeta remainder outside an annulus, for the annulus versus complement-of-ball comparison of the Jacquet window, and in the convergence of the truncated-character local zeta integrals to the coupled local zeta value.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_integrable_levelUniform_dominant_coupledInner.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal in
attribute [local instance] LanglandsTunnell.TateLocal.localBorel in

theorem LanglandsTunnell.CubicInduction.exists_integrable_levelUniform_dominant_coupledInner
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    (∃ D : v.adicCompletion ℚ × v.adicCompletion ℚ → ℝ,
      Integrable D ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))) ∧
      ∀ (c : ℤ) (t : v.adicCompletion ℚ × v.adicCompletion ℚ),
        ‖(charExt (ν 2 * χ)⁻¹ t.1 * ((modulus t.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) t.2 * ((modulus t.2 : ℝ) : ℂ) ^ s) *
            (∫ w : v.adicCompletion ℚ,
              Φ ![t.1, t.2, w] *
                (charExt (ν 0 * (ν 1)⁻¹) (t.2 - t.1 * w) * ((modulus (t.2 - t.1 * w) : ℝ) : ℂ)⁻¹) *
                (if Valued.v (w / (t.2 - t.1 * w)) ≤ WithZero.exp c then
                  (NumberField.StandardAddChar.psiLocal ℚ v (w / (t.2 - t.1 * w)) : ℂ) else 0)
              ∂(selfDualHaarAt ℚ v))‖ ≤ D t) ∧
    (∃ E : ℕ → v.adicCompletion ℚ × v.adicCompletion ℚ → ℝ,
      (∀ m : ℕ, Integrable (E m) ((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v)))) ∧
      (∀ (m : ℕ) (c : ℤ) (t : v.adicCompletion ℚ × v.adicCompletion ℚ),
        ‖(charExt (ν 2 * χ)⁻¹ t.1 * ((modulus t.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) t.2 * ((modulus t.2 : ℝ) : ℂ) ^ s) *
            (∫ w in {w : v.adicCompletion ℚ | Valued.v (t.2 - t.1 * w) ≤ WithZero.exp (-(m : ℤ))},
              Φ ![t.1, t.2, w] *
                (charExt (ν 0 * (ν 1)⁻¹) (t.2 - t.1 * w) * ((modulus (t.2 - t.1 * w) : ℝ) : ℂ)⁻¹) *
                (if Valued.v (w / (t.2 - t.1 * w)) ≤ WithZero.exp c then
                  (NumberField.StandardAddChar.psiLocal ℚ v (w / (t.2 - t.1 * w)) : ℂ) else 0)
              ∂(selfDualHaarAt ℚ v))‖ ≤ E m t) ∧
      Filter.Tendsto
        (fun m : ℕ =>
          ∫ t, E m t ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (mulMeasure (selfDualHaarAt ℚ v))))
        Filter.atTop (nhds 0)) := by sorry
