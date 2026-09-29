-- Prove2me | Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
-- name    : ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/1d73107f-d1f1-5075-beee-77bb400c7de9
-- title:
--   Transcendence and finiteness under constant field extension of F₀
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and assumed algebraic over $\mathbb{Q}$, and let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$, where $\mathbb{Q}((q))$ is `LaurentSeries ℚ`. Write $\iota =$ `coeffEmb L` for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ that applies $\mathbb{Q} \to L$ to each coefficient, and let $LF_0 =$ `laurentBaseChange L F₀` be the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image $\iota(F_0)$. Let $j \in F_0$ be transcendental over $\mathbb{Q}$, and assume $F_0$ is finite-dimensional over the intermediate field $\mathbb{Q}(j)$ obtained by adjoining $j$ to $\mathbb{Q}$ inside $F_0$. Let $jb$ be an element of $LF_0$ whose underlying Laurent series over $L$ equals $\iota$ applied to the Laurent series underlying $j$. Then $jb$ is transcendental over $L$, and $LF_0$ is finite-dimensional over the intermediate field $L(jb)$ obtained by adjoining $jb$ to $L$ inside $LF_0$.
--
--   This is the constant field extension step for a field of $q$-expansions: passing from $\mathbb{Q}$ to an algebraic extension $L$ preserves both the transcendence of a chosen generator and the finiteness of the function field over the rational subfield it generates. These are exactly the two hypotheses required to run the two-chart construction of a smooth proper model of $LF_0/L$ at the generator $jb$, and the result is used in the geometric arguments about models of modular curves, degrees and Riemann–Roch spaces that follow.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
    (L : Type) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) (hj : Transcendental ℚ j)
    [FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) ↥F₀]
    (jb : ↥(laurentBaseChange L F₀))
    (hjb : (jb : LaurentSeries L) = coeffEmb L ((j : ↥F₀) : LaurentSeries ℚ)) :
    Transcendental L jb ∧
      FiniteDimensional ↥(IntermediateField.adjoin L ({jb} : Set ↥(laurentBaseChange L F₀)))
        ↥(laurentBaseChange L F₀) := by sorry
