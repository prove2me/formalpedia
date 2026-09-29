-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
-- name    : NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/402acdbc-f720-517a-873c-e1e4f9c8e1a5
-- title:
--   Fibre integration of the idele norm over a fundamental domain
-- statement:
--   Let $F$ be a number field, equip the idele group $(\mathbb{A}_F)^\times$ of the adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` with a measurable structure that is the Borel structure of its topology, and let $\nu$ be a Haar measure on $(\mathbb{A}_F)^\times$. Write $\|x\| =$ `ideleNorm F x` for the positive real number given by the value at $x$ of the distributive Haar character of $\mathbb{A}_F$. The assertion is the existence of a real constant $C > 0$ such that for every set $\Omega \subseteq (\mathbb{A}_F)^\times$ which is a $\nu$-fundamental domain for the action of the image of $F^\times$ under the map induced by $F \to \mathbb{A}_F$, the following three statements hold. (1) For every measurable $g \colon \mathbb{R} \to \mathbb{C}$, the function $x \mapsto g(\|x\|)$ is integrable on $\Omega$ for $\nu$ if and only if $r \mapsto r^{-1} g(r)$ is integrable on $(0,\infty)$, and $\int_\Omega g(\|x\|)\, d\nu = C \int_0^\infty g(r)\, dr/r$. (2) For every $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$, the function $x \mapsto \|x\|^w$ is integrable on $\Omega \cap \{\|x\| \le 1\}$ with integral $C/w$, and $x \mapsto \|x\|^{-w}$ is integrable on $\Omega \cap \{\|x\| \ge 1\}$ with integral $C/w$. (3) For every homomorphism $\chi \colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ which is trivial on the principal ideles, satisfies $|\chi(x)| = 1$ for all $x$ and is continuous as a $\mathbb{C}$-valued function, and for every $w$ with $\operatorname{Re} w > 0$: the functions $x \mapsto \chi(x)\|x\|^{w}$ and $x \mapsto \chi(x)\|x\|^{-w}$ are integrable on $\Omega \cap \{\|x\| \le 1\}$ and on $\Omega \cap \{\|x\| \ge 1\}$ respectively; if $\chi$ is non-trivial on some idele of norm $1$ then both integrals vanish; and if $\chi(z) = 1$ for every $z$ with $\|z\| = 1$, then there is $\tau \in \mathbb{R}$ with $\chi =$ `normPowChar F τ`, i.e. $\chi(x) = \|x\|^{i\tau}$, and the two integrals equal $C/(w + i\tau)$ and $C/(w - i\tau)$ respectively.
--
--   This is the global part of Tate's analysis of the zeta integral: measure-theoretically it says that pushing $\nu|_\Omega$ forward along $\log\|\cdot\|$ gives $C$ times Lebesgue measure, so that the idele class group splits as the norm-one class group of volume $C$ times $(0,\infty)$ with $dr/r$, and it records the resulting pole terms $C/w$, $C/(w \pm i\tau)$ together with the vanishing for characters non-trivial on the norm-one ideles. It is used in the constant terms and Maass–Selberg type computations for pseudo-Eisenstein series and in convergence estimates for Godement sections on adelic $GL_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
        (∀ g : ℝ → ℂ, Measurable g →
          (IntegrableOn (fun x => g (NumberField.TateGlobal.ideleNorm F x)) Ω ν ↔
              IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Set.Ioi (0 : ℝ))) ∧
          ∫ x in Ω, g (NumberField.TateGlobal.ideleNorm F x) ∂ν =
            C * ∫ r in Set.Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r) ∧
        (∀ w : ℂ, 0 < w.re →
          IntegrableOn (fun x => ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w)
              (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1}) ν ∧
          ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
              ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = C / w ∧
          IntegrableOn (fun x => ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w))
              (Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x}) ν ∧
          ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
              ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = C / w) ∧
        (∀ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ →
          AutomorphicForm.IsUnitaryChar (𝓞 F) F χ →
          Continuous (fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) →
          ∀ w : ℂ, 0 < w.re →
            IntegrableOn (fun x => ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w)
                (Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1}) ν ∧
            IntegrableOn (fun x => ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w))
                (Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x}) ν ∧
            ((∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 ∧ χ z ≠ 1) →
              ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
                  ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν = 0 ∧
              ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
                  ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν = 0) ∧
            ((∀ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 → χ z = 1) →
              ∃ τ : ℝ, χ = NumberField.TateGlobal.normPowChar F τ ∧
                ∫ x in Ω ∩ {x | NumberField.TateGlobal.ideleNorm F x ≤ 1},
                    ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ w ∂ν =
                  C / (w + (τ : ℂ) * Complex.I) ∧
                ∫ x in Ω ∩ {x | 1 ≤ NumberField.TateGlobal.ideleNorm F x},
                    ((χ x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F x : ℝ) : ℂ) ^ (-w) ∂ν =
                  C / (w - (τ : ℂ) * Complex.I))) := by sorry
