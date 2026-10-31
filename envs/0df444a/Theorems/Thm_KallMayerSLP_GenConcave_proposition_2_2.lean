-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_proposition_2_2
-- name    : KallMayerSLP.GenConcave.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:40.434019+00:00
-- url     : https://prove2.me/theorems/ca329ac1-288a-4599-a9f7-e1d48f21c37e
-- title:
--   Proposition 2.2 — translates of a closed convex set have $\gamma$-concave probability
-- statement:
--   Let $\xi$ be an $r$-dimensional random vector with law $\mathbb P_\xi$ on the Borel sets of $\mathbb R^r$. For a convex closed set $A\subseteq\mathbb R^r$ define
--
--   $$
--   \Gamma_A(y)=\mathbb P_\xi\bigl(A+\{y\}\bigr),\qquad y\in\mathbb R^r.
--   $$
--
--   If $\mathbb P_\xi$ is a $\gamma$-concave measure, then $\Gamma_A$ is a $\gamma$-concave function.
--
--   With $A=\mathbb R^r_-$ this gives $\gamma$-concavity of the distribution function $F_\xi$, which is the route from concavity properties of a measure to convexity of probability constraints.
--
--   **Formalization Note** The law $\mathbb P_\xi$ is a measure $\mu$ on `Fin r → ℝ`; every probability measure is the law of a random vector, so nothing is lost. $\Gamma_A(y)$ is a real number.
--
--   Differences from the source:
--   - encoding: law $\mathbb P_\xi$ of a random vector $\xi$ → a measure $\mu$ on $\mathbb R^r$ ($\gamma$-concavity includes being a probability measure); reason: every probability measure is the law of the identity map, same instances
--   - generalization: §2.5.1 assumes throughout that $P_\xi$ is absolutely continuous (p.122) → any $\gamma$-concave probability measure, with or without a density; reason: the proof never uses the density, and the absolutely continuous laws are a special case
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 2.2, p.126 (PDF 136)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveMeasure

open MeasureTheory
open scoped Pointwise

namespace KallMayerSLP.GenConcave

/-- **Proposition 2.2** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2,
p. 126, PDF p. 136). Let `ℙ_ξ` be the law of a random vector `ξ` on the Borel sets of
`ℝ^r`, and for a convex closed set `A ⊆ ℝ^r` let `Γ_A(y) = ℙ_ξ(A + {y})`. If `ℙ_ξ` is a
`γ`-concave measure, then `Γ_A` is a `γ`-concave function.

**Formalization Note.** The law `ℙ_ξ` is a measure `μ` on `Fin r → ℝ` (every probability
measure is the law of the identity map, so nothing is lost); `A + {y}` is the pointwise
sum; `Γ_A(y)` is the real number `(μ (A + {y})).toReal`. -/
theorem proposition_2_2 {r : ℕ} (γ : EReal) (μ : Measure (Fin r → ℝ))
    (hμ : IsGammaConcaveMeasure γ μ) (A : Set (Fin r → ℝ)) (hA : Convex ℝ A)
    (hAc : IsClosed A) :
    IsGammaConcaveFun γ (fun y : Fin r → ℝ => (μ (A + {y})).toReal) := by sorry

end KallMayerSLP.GenConcave
