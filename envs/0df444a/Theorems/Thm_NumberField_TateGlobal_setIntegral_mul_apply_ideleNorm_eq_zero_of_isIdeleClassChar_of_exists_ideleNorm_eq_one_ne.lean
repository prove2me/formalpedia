-- Prove2me | Theorems.Thm_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
-- name    : NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/6cd9bec9-9a46-5ea6-85e2-baf95e94b6a7
-- title:
--   Vanishing of int_Ω χ(a)g(‖a‖) dν for χ nontrivial on norm-one ideles
-- statement:
--   Let $F$ be a number field and consider the unit group $(\mathbb{A}_F)^\times$ of its adele ring, equipped with a measurable space structure that is the Borel structure of its topology. Let $\nu$ be a left-invariant measure on $(\mathbb{A}_F)^\times$, and let $\Omega \subseteq (\mathbb{A}_F)^\times$ be a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain` for $\nu$, for the subgroup given by the range of the map $F^\times \to (\mathbb{A}_F)^\times$ induced by the structure map $F \to \mathbb{A}_F$, i.e. for the group of principal ideles. Let $\chi : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be a group homomorphism satisfying [`AutomorphicForm.IsIdeleClassChar`](def/AutomorphicForm_AdelicLsXi.html#L21), which by definition means $\chi(\iota(u)) = 1$ for every $u \in F^\times$, where $\iota$ is the above map on units; no continuity or unitarity is assumed. Assume further that there exists an idele $z$ with $\chi(z) \neq 1$ whose idele norm is $1$, the idele norm of $x$ being the real number underlying $\mathrm{distribHaarChar}(\mathbb{A}_F)(x)$, the modulus of scaling by $x$ on the adele ring. Then for every function $g : \mathbb{R} \to \mathbb{C}$, with no measurability or integrability hypothesis, $\int_\Omega \chi(a)\,g(\|a\|)\,d\nu(a) = 0$, where $\|a\|$ denotes the idele norm.
--
--   This is the orthogonality (or Mellin-orthogonality) step in Tate's theory of global zeta functions: an idele class character that is nontrivial on the norm-one ideles kills any integral over a fundamental domain of a function depending only on the idele norm. It is used in the analytic treatment of pseudo-Eisenstein series and Maass–Selberg computations, where several cross terms in inner products are shown to vanish for this reason.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ)
    (hχ : ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 ∧ χ z ≠ 1)
    (g : ℝ → ℂ) :
    ∫ a in Ω, ((χ a : ℂˣ) : ℂ) * g (NumberField.TateGlobal.ideleNorm F a) ∂ν = 0 := by sorry
