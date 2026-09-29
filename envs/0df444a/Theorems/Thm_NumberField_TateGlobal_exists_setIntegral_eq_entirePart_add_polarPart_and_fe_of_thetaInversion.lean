-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
-- name    : NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/f56f288e-e7c3-5475-8078-4d3b661c69e2
-- title:
--   Tate's main theorem: entire part plus polar part
-- statement:
--   Let $F$ be a number field, and let $\nu$ be a Haar measure on the idele group $(\mathbb{A}_F)^\times$ (with its Borel structure); write $\|t\| =$ `ideleNorm F t`, the real number given by the value at $t$ of the distributive Haar character of $\mathbb{A}_F$. The assertion is that there is a constant $C>0$, depending only on $F$ and $\nu$, such that the following holds for every set $\Omega \subseteq (\mathbb{A}_F)^\times$ that is a fundamental domain for the action of the subgroup of principal ideles (the range of $F^\times \to (\mathbb{A}_F)^\times$) with respect to $\nu$, every homomorphism $\chi \colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ that is trivial on principal ideles, satisfies $|\chi(x)| = 1$ for all $x$ and is continuous, every pair of functions $\theta, \theta' \colon (\mathbb{A}_F)^\times \to \mathbb{C}$ with $\theta'$ invariant under multiplication by principal ideles, and all $a,b \in \mathbb{C}$ and real $d>0$ subject to the inversion relation $\theta(t) + a = \|t\|^{-d}\bigl(\theta'(t^{-1}) + b\bigr)$ for all $t$ and to the hypothesis that, for every real $\sigma$, both $\theta(t)\|t\|^{\sigma}$ and $\theta'(t)\|t\|^{\sigma}$ are integrable on $\Omega \cap \{\,1 \le \|t\|\,\}$: there exist functions $R, R' \colon \mathbb{C} \to \mathbb{C}$ such that, for every $s$,
--   $$R(s) = \int_{\Omega \cap \{1 \le \|t\|\}} \theta\,\chi\,\|t\|^{s}\,d\nu + \int_{\Omega \cap \{1 \le \|t\|\}} \theta'\,\chi^{-1}\,\|t\|^{d-s}\,d\nu,$$
--   and symmetrically $R'(s)$ with the roles of $(\theta,\chi)$ and $(\theta',\chi^{-1})$ exchanged (the integrals being the Bochner integrals, so that these equalities are asserted for all $s$), and such that: $R(s) = R'(d-s)$ for all $s$; if $\chi \ne \|\cdot\|^{i\tau}$ (i.e. $\chi \ne$ `normPowChar F τ`) for every real $\tau$, then $\int_{\Omega} \theta\,\chi\,\|t\|^{s}\,d\nu = R(s)$ and $\int_{\Omega} \theta'\,\chi^{-1}\,\|t\|^{s}\,d\nu = R'(s)$ for $\operatorname{Re} s > d$; for every real $\tau$ with $\chi = \|\cdot\|^{i\tau}$ and every $s$ with $\operatorname{Re} s > d$, the same two integrals equal $R(s) + Cb/(s-d+i\tau) - Ca/(s+i\tau)$ and $R'(s) + Ca/(s-d-i\tau) - Cb/(s-i\tau)$ respectively; and, finally, there are $c_1, c_0, p_1, p_0 \in \mathbb{C}$ with $c_1 = c_0 = 0$ whenever $\chi$ is no $\|\cdot\|^{i\tau}$, such that for $\operatorname{Re} s > d$ the first integral equals $R(s) + c_1/(s-p_1) + c_0/(s-p_0)$ and the second equals $R'(s) - \bigl(c_1/(s-(d-p_1)) + c_0/(s-(d-p_0))\bigr)$.
--
--   This is the main theorem of Tate's thesis on global zeta integrals, in an abstract form whose only input is a pair of theta functions linked by a Poisson-type inversion relation with parameter $d$, so that the case $d=1$ covers Hecke $L$-functions and $d=2$ the integral representing the Godement–Eisenstein series on $\mathrm{GL}_2$; the final clause packages the continuation as an entire part $R$ plus a polar part with at most two simple poles, symmetric under $s \mapsto d-s$. It is used in the Rankin–Selberg input to the Langlands–Tunnell theorem, for Godement–Eisenstein integrals attached to Schwartz–Bruhat functions of two adelic variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Set (AdeleRing (𝓞 F) F)ˣ),
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
      ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ →
        AutomorphicForm.IsUnitaryChar (𝓞 F) F χ →
        Continuous (fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) →
      ∀ (θ θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ),
        (∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
          θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t) →
      ∀ (a b : ℂ) (d : ℝ), 0 < d →
        (∀ t : (AdeleRing (𝓞 F) F)ˣ,
          θ t + a = ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b)) →
        (∀ σ : ℝ, IntegrableOn
          (fun t => θ t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
          (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) →
        (∀ σ : ℝ, IntegrableOn
          (fun t => θ' t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
          (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) →
        ∃ R R' : ℂ → ℂ,
          (∀ s : ℂ, R s =
            ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
              + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν) ∧
          (∀ s : ℂ, R' s =
            ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
              + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν) ∧
          (∀ s : ℂ, R s = R' ((d : ℂ) - s)) ∧
          ((∀ τ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar F τ) →
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν = R s) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν = R' s)) ∧
          (∀ τ : ℝ, χ = NumberField.TateGlobal.normPowChar F τ →
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R s + C * b / (s - d + (τ : ℂ) * Complex.I) - C * a / (s + (τ : ℂ) * Complex.I)) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R' s + C * a / (s - d - (τ : ℂ) * Complex.I) - C * b / (s - (τ : ℂ) * Complex.I))) ∧
          (∃ c₁ c₀ p₁ p₀ : ℂ,
            ((∀ τ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar F τ) → c₁ = 0 ∧ c₀ = 0) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R s + (c₁ / (s - p₁) + c₀ / (s - p₀))) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R' s - (c₁ / (s - ((d : ℂ) - p₁)) + c₀ / (s - ((d : ℂ) - p₀))))) := by sorry
