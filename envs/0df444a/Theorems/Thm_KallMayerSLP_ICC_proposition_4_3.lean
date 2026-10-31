-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_proposition_4_3
-- name    : KallMayerSLP.ICC.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:39.593558+00:00
-- url     : https://prove2.me/theorems/523f610c-67da-40b9-a682-23303aacc739
-- title:
--   Proposition 4.3 — $H_J$ and $K_J$ are convex
-- statement:
--   Let $\xi$ have law $P$, and suppose the expected values of $T(\xi)$ and $h(\xi)$ exist. Then
--   $$
--   H_J(x)=\mathbb E_\xi\Big[\max_{1\le i\le s}\zeta_i^-(x,\xi)\Big],\qquad
--   K_J(x)=\mathbb E_\xi\Big[\max_{1\le i\le s}\zeta_i^+(x,\xi)\Big]
--   $$
--   are convex functions on $\mathbb R^n$. This holds for a random technology matrix and with no restriction on the distribution of $\xi$ beyond the existence of the expected value.
--
--   Differences from the source:
--
--   - generalization: ξ is a random vector in ℝʳ, T(ξ), h(ξ) affine in ξ (1.2), law ℙ_ξ → Ξ any measurable space, P any probability measure on Ξ, T, h arbitrary functions with integrable entries; reason: the book says (1.2) is not used in the chapter; Ξ = ℝʳ with P = ℙ_ξ gives the book's case
--   - generalization: s > 1 (§4.1.2) → every s ≥ 1; reason: the s = 1 case is covered by the same statement
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 4.3, p.155 (PDF 165)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_KJ
import Definitions.Def_KallMayerSLP_ICC_HJ

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **Proposition 4.3 (joint integrated probability functions are convex).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Proposition 4.3, p.155 (PDF 165).
Both `H_J(x)` and `K_J(x)` are convex functions on `ℝⁿ`.

**Formalization Note.** "The convexity property holds also for a random technology matrix and
without any restriction on the probability distribution of `ξ`, beyond the existence of the
expected value" (p.155): the only assumptions are `hT` and `hh`, the standing assumption of §4.1
(p.149), read entrywise. -/
theorem proposition_4_3 {Ξ : Type*} [MeasurableSpace Ξ] {s n : ℕ} [Nonempty (Fin s)]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ)
    (hT : ∀ i j, Integrable (fun ξ => T ξ i j) P) (hh : ∀ i, Integrable (fun ξ => h ξ i) P) :
    ConvexOn ℝ Set.univ (HJ P T h) ∧ ConvexOn ℝ Set.univ (KJ P T h) := by sorry

end KallMayerSLP.ICC
