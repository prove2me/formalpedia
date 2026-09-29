-- Prove2me | Theorems.Thm_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
-- name    : NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/17bca532-c978-5ea7-9d83-5fb6afecfd58
-- title:
--   Affine invariance of adelic box integrals of F-periodic functions
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` carried with its Borel $\sigma$-algebra and the additive Haar measure `adelicAddHaar`. Let $h\colon \mathbb{A}_F \to [0,\infty]$ be a measurable function which is invariant under translation by principal adeles, i.e. $h(\iota(\beta) + u) = h(u)$ for all $\beta \in F$ and $u \in \mathbb{A}_F$, where $\iota$ is the structure map $F \to \mathbb{A}_F$. Let $a \in F^\times$ be a unit of $F$ and $u_0 \in \mathbb{A}_F$. Then the lower Lebesgue integrals of $u \mapsto h(\iota(a)u + u_0)$ and of $h$ over the set `adelicBox F` agree. Here `adelicBox F` consists of those adeles whose archimedean component lies in the preimage, under the identification of $\mathbb{A}_{F,\infty}$ with the mixed space $F \otimes \mathbb{R}$, of the $\mathbb{Z}$-span fundamental domain of the lattice basis given by the canonical embedding of $F$, and whose finite component is integral at every height one prime of $\mathcal{O}_F$, that is, lies in $\mathcal{O}_{F_v}$ for all $v$.
--
--   The adelic box is a fundamental domain for the translation action of the principal subgroup $F \subset \mathbb{A}_F$, so the statement says that the integral of an $F$-periodic function over $F \backslash \mathbb{A}_F$ is unchanged by the affine substitution $u \mapsto au + u_0$ with $a \in F^\times$. It is used in the computation of Petersson-type integrals against Bruhat–Eisenstein series in terms of Whittaker coefficients, where such substitutions arise from the action of rational diagonal elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem NumberField.AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
    (F : Type) [Field F] [NumberField F]
    (h : AdeleRing (𝓞 F) F → ℝ≥0∞) (hh : Measurable h)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F), h (algebraMap F (AdeleRing (𝓞 F) F) β + u) = h u)
    (a : Fˣ) (u₀ : AdeleRing (𝓞 F) F) :
    ∫⁻ u in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) a * u + u₀) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ u in adelicBox F, h u ∂(adelicAddHaar (𝓞 F) F) := by sorry
