-- Prove2me | Theorems.Thm_NatureSLT_GrowthFunction_vcDim_sin_infinite
-- name    : NatureSLT.GrowthFunction.vcDim_sin_infinite
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:54.800819+00:00
-- url     : https://prove2.me/theorems/411fad3b-0a6d-4758-a75e-208a86218619
-- title:
--   Section 3.6, Example 2(i) — θ(sin αz) has infinite VC dimension
-- statement:
--   Consider the set of indicator functions on the real line
--
--   $$f(z, \alpha) = \theta(\sin \alpha z), \qquad \alpha \in \mathbb R^1,$$
--
--   where $\theta(u) = 0$ for $u < 0$ and $\theta(u) = 1$ for $u \ge 0$. Then:
--
--   1. for every $\ell \ge 1$ the points $z_1 = 10^{-1}, \dots, z_\ell = 10^{-\ell}$ are shattered, and explicitly: for every sequence $\delta_1, \dots, \delta_\ell \in \{0, 1\}$, the parameter
--   $$\alpha = \pi\left(\sum_{i=1}^{\ell} (1 - \delta_i) 10^i + 1\right)$$
--   satisfies $\theta(\sin \alpha z_i) = \delta_i$ for every $i = 1, \dots, \ell$;
--   2. consequently the VC dimension of the set is infinite.
--
--   The example shows that a set of functions with a single parameter can have infinite VC dimension: the VC dimension does not coincide with the number of parameters.
--
--   **Formalization Note** Indices run from $0$ in the formal statement: the book's index $i \in \{1, \dots, \ell\}$ is $i + 1$ for $i \in \{0, \dots, \ell - 1\}$, so $z_i = 10^{-(i+1)}$ and the sum is $\sum_{j} (1 - \delta_j) 10^{j+1}$. Each $\delta_i$ is a boolean (`true` = $1$), and $1 - \delta_i$ is written as $0$ if $\delta_i = 1$ and $1$ otherwise. The case $\ell = 0$ is included and empty.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 82, Section 3.6, Example 2(i)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_NatureSLT_GrowthFunction_stepFunction

namespace NatureSLT.GrowthFunction

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 82, Example 2(i): the
VC dimension of `f(z, α) = θ(sin αz)`, `α ∈ ℝ¹`, is infinite. The points `zᵢ = 10^{-i}`,
`i = 1, …, ℓ`, are shattered: for `δ₁, …, δ_ℓ ∈ {0, 1}` the parameter
`α = π (∑_{i=1}^ℓ (1 − δᵢ) 10^i + 1)` gives `θ(sin α zᵢ) = δᵢ` for every `i`. Indices are
`0`-based here (`i ↦ i + 1`), `δᵢ` is a `Bool` (`true` = `1`), and `θ(0) = 1`. -/
theorem vcDim_sin_infinite :
    (∀ (ℓ : ℕ) (δ : Fin ℓ → Bool) (i : Fin ℓ),
      stepFunction (Real.sin
        ((Real.pi * (∑ j : Fin ℓ, (if δ j then (0 : ℝ) else 1) * (10 : ℝ) ^ ((j : ℕ) + 1) + 1)) *
          ((10 : ℝ) ^ ((i : ℕ) + 1))⁻¹)) = δ i) ∧
    vcDim (fun (α : ℝ) (z : ℝ) => stepFunction (Real.sin (α * z))) = ⊤ := by sorry

end NatureSLT.GrowthFunction
