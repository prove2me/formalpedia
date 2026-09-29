-- Prove2me | Theorems.Thm_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion
-- name    : NumberField.TateGlobal.setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/10941ec5-33a6-5fff-801d-09c1e2909fa7
-- title:
--   Tate's truncated zeta integral under theta inversion
-- statement:
--   Let $F$ be a number field, let $\nu$ be a Haar measure on the idele group $(\mathbb{A}_F)^\times$ (with its Borel $\sigma$-algebra), and let $\Omega$ be a fundamental domain for the action on $(\mathbb{A}_F)^\times$ of the image of $F^\times$ under the map induced by $F \to \mathbb{A}_F$. Write $\|t\| = \mathrm{distribHaarChar}(\mathbb{A}_F)(t)$, viewed as a real number, for the idele norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19). Let $\chi \colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be a homomorphism which is trivial on the principal ideles, satisfies $|\chi(x)| = 1$ for all $x$, and is continuous as a $\mathbb{C}$-valued function. Let $\theta, \theta' \colon (\mathbb{A}_F)^\times \to \mathbb{C}$, with $\theta'$ invariant under multiplication by principal ideles (no invariance is assumed of $\theta$), let $a, b \in \mathbb{C}$ and $d > 0$ real, and assume the inversion relation $\theta(t) + a = \|t\|^{-d}(\theta'(t^{-1}) + b)$ for all $t$, together with, for every real $\sigma$, integrability of $t \mapsto \theta(t)\|t\|^{\sigma}$ and of $t \mapsto \theta'(t)\|t\|^{\sigma}$ on $\Omega \cap \{\|t\| \ge 1\}$ with respect to $\nu$. The conclusion has two parts. First, for every $s \in \mathbb{C}$ both $t \mapsto \theta(t)\chi(t)\|t\|^{s}$ and $t \mapsto \theta'(t)\chi(t)^{-1}\|t\|^{s}$ are integrable on $\Omega \cap \{\|t\| \ge 1\}$. Second, for every $s$ with $\operatorname{Re} s > d$, the function $t \mapsto \theta(t)\chi(t)\|t\|^{s}$ is integrable on $\Omega$ and on $\Omega \cap \{\|t\| \le 1\}$, and $$\int_{\Omega \cap \{\|t\| \le 1\}} \theta\chi\|\cdot\|^{s} \, d\nu = \int_{\Omega \cap \{\|t\| \ge 1\}} \theta'\chi^{-1}\|\cdot\|^{d-s} \, d\nu + b\int_{\Omega \cap \{\|t\| \le 1\}} \chi\|\cdot\|^{s-d} \, d\nu - a\int_{\Omega \cap \{\|t\| \le 1\}} \chi\|\cdot\|^{s} \, d\nu,$$ whence also $\int_{\Omega} \theta\chi\|\cdot\|^{s} \, d\nu$ equals the integral of $\theta\chi\|\cdot\|^{s}$ over $\Omega \cap \{\|t\| \ge 1\}$ plus the right-hand side above.
--
--   This is the measure-theoretic step in Tate's method: the part of a global zeta integral over the ideles of norm at most $1$ is rewritten, by the inversion relation for the pair $(\theta,\theta')$, as the dual integral over the ideles of norm at least $1$ corrected by the two integrals producing the poles. Stated for abstract $\theta, \theta'$ and an arbitrary exponent $d > 0$, it is used by [`NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion`](thm.html#NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion) to split a global zeta integral into an entire part and a polar part and to obtain the functional equation $s \mapsto d - s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.TateGlobal.setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ)
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    (θ θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hθ' : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t)
    (a b : ℂ) (d : ℝ) (hd : 0 < d)
    (hrel : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      θ t + a = ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b))
    (hdec : ∀ σ : ℝ, IntegrableOn
      (fun t => θ t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν)
    (hdec' : ∀ σ : ℝ, IntegrableOn
      (fun t => θ' t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) :
    (∀ s : ℂ,
      IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s)
        (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν ∧
      IntegrableOn (fun t => θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s)
        (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) ∧
    (∀ s : ℂ, d < s.re →
      IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s) Ω ν ∧
      IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s)
        (Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1}) ν ∧
      ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
          θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
        ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
            θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν
          + b * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (s - d) ∂ν
          - a * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν ∧
      ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
        ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
            θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
          + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
              θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν
          + b * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (s - d) ∂ν
          - a * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν) := by sorry
