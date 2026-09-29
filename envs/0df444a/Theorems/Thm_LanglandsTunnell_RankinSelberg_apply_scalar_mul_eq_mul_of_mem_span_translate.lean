-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_apply_scalar_mul_eq_mul_of_mem_span_translate
-- name    : LanglandsTunnell.RankinSelberg.apply_scalar_mul_eq_mul_of_mem_span_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f1394cd7-cc18-51e9-88d5-cd19886d8c2c
-- title:
--   Central transformation law extends to the span of right translates
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$, and write $F = \mathbb{Q}_p$ for the completion of $\mathbb{Q}$ at $p$. Let $\theta_0 \colon F^{\times} \to \mathbb{C}^{\times}$ be a homomorphism of monoids (a quasi-character of $F^{\times}$, with no continuity required), and let $w_{2,\mathrm{base}} \colon \mathrm{GL}_2(F) \to \mathbb{C}$ be an arbitrary function satisfying the transformation law $w_{2,\mathrm{base}}(\mathrm{scalar}(z) \cdot g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$ for every $z \in F^{\times}$ and every $g \in \mathrm{GL}_2(F)$, where $\mathrm{scalar}(z)$ denotes the scalar matrix $z \cdot I_2$ viewed in $\mathrm{GL}_2(F)$. The assertion is that every element $w$ of the $\mathbb{C}$-linear span, inside the space of all functions $\mathrm{GL}_2(F) \to \mathbb{C}$, of the set of right translates $g \mapsto w_{2,\mathrm{base}}(g h)$ for $h$ ranging over $\mathrm{GL}_2(F)$, obeys the same law: $w(\mathrm{scalar}(z) \cdot g) = \theta_0(z)\, w(g)$ for all $z \in F^{\times}$ and all $g \in \mathrm{GL}_2(F)$.
--
--   This records that the central transformation law of a single vector propagates to the whole space it generates under right translation, so that the span of the right translates of $w_{2,\mathrm{base}}$ is a space of functions with central character $\theta_0$. It is used in the local Rankin–Selberg computations, in [`LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le), to pull a scalar out of the value of a Whittaker-type function at a diagonal element times a maximal compact element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_apply_scalar_mul_eq_mul_of_mem_span_translate.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.apply_scalar_mul_eq_mul_of_mem_span_translate
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g := by sorry
