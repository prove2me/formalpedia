-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
-- name    : LanglandsTunnell.CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/4e519f48-8798-59eb-ad0a-f1c18c6c7a20
-- title:
--   Non-norm condition is stable under twisting by base-changed characters
-- statement:
--   Let $K$ be a number field, equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$, let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb{C}^\times$ and $\chi$ one from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$, both admissible twists, that is, trivial on the principal ideles coming from $K^\times$ (respectively $\mathbb{Q}^\times$), continuous, and of absolute value $1$ at every idele. Assume that no admissible twist $\eta$ of $\mathbb{Q}$ satisfies: for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified (all local units at $\mathfrak{P}$ whose inverse is also integral have local character value $1$) and such that $\eta$ is unramified at the prime $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ below it, the value of $\mu$ at the idele which is a uniformiser at $\mathfrak{P}$ and $1$ elsewhere equals the corresponding value of $\eta$ at the prime below, raised to the power $\mathrm{inertiaDeg}'$ of $\mathfrak{P}$ over that prime. The conclusion is that the same fails for the twisted character $\mu\cdot(\chi\circ\mathrm{idelicNorm})$, where $\mathrm{idelicNorm}$ is the norm map on ideles attached to the base change $\mathbb{Q}\to K$: no admissible twist $\eta$ of $\mathbb{Q}$ has that property with $\mu$ replaced by $\mu\cdot(\chi\circ\mathrm{idelicNorm})$.
--
--   This records that the condition "$\mu$ does not come from a character of $\mathbb{Q}$ by composition with the idelic norm", in the uniformiser-by-uniformiser form used to test it, is unaffected by twisting $\mu$ by the base change to $K$ of a character of $\mathbb{Q}$; the non-norm condition is what guarantees that the representation induced from $\mu$ is irreducible, hence that the associated automorphic object is cuspidal. It is used in the construction of the cubic induction data underlying the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

theorem LanglandsTunnell.CubicInduction.not_exists_eq_pow_inertiaDeg_mul_comp_idelicNorm_of_not_exists
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)) :
    ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt
          (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        (((μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
            (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by sorry
