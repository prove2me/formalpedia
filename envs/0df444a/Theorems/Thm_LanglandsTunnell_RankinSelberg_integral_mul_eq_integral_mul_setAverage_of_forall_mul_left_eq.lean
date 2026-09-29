-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_mul_eq_integral_mul_setAverage_of_forall_mul_left_eq
-- name    : LanglandsTunnell.RankinSelberg.integral_mul_eq_integral_mul_setAverage_of_forall_mul_left_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/c240f195-eb4d-5b99-ba73-c2de827517f0
-- title:
--   Left averaging over a compact open subgroup under a Haar integral
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$, i.e. an element of the height one spectrum of $\mathcal{O}_{\mathbb{Q}}$, and equip $G = \mathrm{GL}_2(\mathbb{Q}_p)$, where $\mathbb{Q}_p$ denotes the $p$-adic completion of $\mathbb{Q}$, with the Borel $\sigma$-algebra of its topology (`localGLBorel`, together with the corresponding `BorelSpace` instance). The assertion is: for every Haar measure $\mu_2$ on $G$, every subgroup $K \le G$ whose underlying set is open and compact, and all measurable functions $\Theta, L \colon G \to \mathbb{C}$ such that $\Theta(kg) = \Theta(g)$ for all $k \in K$ and all $g \in G$, and such that $g \mapsto \Theta(g) L(g)$ is $\mu_2$-integrable, two conclusions hold simultaneously: first, the function
--   $$g \mapsto \Theta(g)\,\Bigl(\mu_2(K)^{-1}\int_K L(kg)\,d\mu_2(k)\Bigr)$$
--   is $\mu_2$-integrable, the normalising factor being the inverse of the real number $\mu_2(K)$ viewed in $\mathbb{C}$; and second,
--   $$\int_G \Theta(g) L(g)\,d\mu_2(g) \;=\; \int_G \Theta(g)\,\Bigl(\mu_2(K)^{-1}\int_K L(kg)\,d\mu_2(k)\Bigr)\,d\mu_2(g).$$
--   Only left invariance of $\mu_2$ and left $K$-invariance of $\Theta$ enter.
--
--   This is the standard device of replacing a local integrand by its average over a compact open subgroup when the companion factor is invariant under that subgroup. It is used in the local Rankin–Selberg computations for $\mathrm{GL}_2(\mathbb{Q}_p)$, in both the principal series and cuspidal branches of the local functional equation for the relevant zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integral_mul_eq_integral_mul_setAverage_of_forall_mul_left_eq.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.RankinSelberg.integral_mul_eq_integral_mul_setAverage_of_forall_mul_left_eq
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ (Θ L : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), Measurable Θ → Measurable L →
        (∀ k ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), Θ (k * g) = Θ g) →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => Θ g * L g) μ₂ →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            Θ g * (((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
              ∫ k in (K : Set (GL (Fin 2) (p.adicCompletion ℚ))), L (k * g) ∂μ₂)) μ₂ ∧
        ∫ g, Θ g * L g ∂μ₂ =
          ∫ g, Θ g * (((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
              ∫ k in (K : Set (GL (Fin 2) (p.adicCompletion ℚ))), L (k * g) ∂μ₂) ∂μ₂ := by sorry
