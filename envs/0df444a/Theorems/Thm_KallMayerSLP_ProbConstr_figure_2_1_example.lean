-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_figure_2_1_example
-- name    : KallMayerSLP.ProbConstr.figure_2_1_example
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:08.142642+00:00
-- url     : https://prove2.me/theorems/ac450c7c-6704-4380-9963-645ad5220b4d
-- title:
--   Figure 2.1, pp.98–99 — $\mathcal B(3/4)=[K_1\cap K_2]\cup[K_2\cap K_3]$ is not convex
-- statement:
--   Let $\xi$ have a finite discrete distribution with three realizations of probabilities $p_1=\tfrac14$, $p_2=\tfrac12$, $p_3=\tfrac14$, and let the data be such that the realized constraint sets in $\mathbb R^2$ are
--   $$
--   \begin{aligned}
--   K_1&=\{x\in\mathbb R^2\mid x_1-x_2\ge-2,\ x_2\ge3\},\\
--   K_2&=\{x\in\mathbb R^2\mid x_1-x_2\ge0,\ 2x_1+3x_2\le25\},\\
--   K_3&=\{x\in\mathbb R^2\mid x_1+x_2\le8,\ -x_1+3x_2\ge0\}.
--   \end{aligned}
--   $$
--   Then at the level $\alpha=\tfrac34$
--   $$
--   \mathcal B(\alpha)=[K_1\cap K_2]\cup[K_2\cap K_3],
--   $$
--   and $\mathcal B(\alpha)$ is not convex.
--
--   The example shows that $\mathcal B(\alpha)$ can fail to be convex for a finite discrete distribution at a level below the thresholds of Theorems 2.3 and 2.4.
--
--   Differences from the source:
--   - reading: the sets K_1, K_2, K_3 and the probabilities, with no data T, h, ξ̂ given → every tableau with p = (1/4, 1/2, 1/4) and every data T, h (any r, any number m of rows) whose realized sets are the three printed sets; reason: the book specifies only the K_j; B(α) depends on the data only through the K_j and p
--   - encoding: indices 1, 2, 3 and coordinates x_1, x_2 → Fin 3 indices 0, 1, 2 and coordinates x 0, x 1; reason: renaming only
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, p.98 (PDF 108), example from Kall [134], and Figure 2.1, p.99 (PDF 109)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_realizationSet
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet
import Definitions.Def_KallMayerSLP_ProbConstr_RealizationTableau_measure

namespace KallMayerSLP.ProbConstr

/-- The example of Figure 2.1 (from Kall [134]): three realizations with
`K₁ = {x ∈ ℝ² | x₁ − x₂ ≥ −2, x₂ ≥ 3}`, `K₂ = {x ∈ ℝ² | x₁ − x₂ ≥ 0, 2x₁ + 3x₂ ≤ 25}`,
`K₃ = {x ∈ ℝ² | x₁ + x₂ ≤ 8, −x₁ + 3x₂ ≥ 0}` and probabilities `p₁ = 1/4`, `p₂ = 1/2`,
`p₃ = 1/4`, at level `α = 3/4`: the feasible domain is non-convex and
`B(α) = [K₁ ∩ K₂] ∪ [K₂ ∩ K₃]`.

Kall & Mayer 2005, Chapter 2, §2.2, p.98 (PDF 108), and Figure 2.1, p.99 (PDF 109).

**Formalization Note.** Indices `0, 1, 2` stand for the book's `1, 2, 3`, coordinates `x 0`,
`x 1` for `x₁`, `x₂`. The book gives the sets `K_j` and not the data; the theorem holds for every
tableau with these probabilities and every data `T`, `h` (any number `m` of rows, any `r`) whose
realized sets `K_j = {x | T(ξ̂^j)x ≥ h(ξ̂^j)}` are the three printed sets. -/
theorem figure_2_1_example {r m : ℕ} (τ : RealizationTableau 3 r)
    (hp : τ.p 0 = 1 / 4 ∧ τ.p 1 = 1 / 2 ∧ τ.p 2 = 1 / 4)
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin 2) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ)
    (hK₁ : realizationSet T h (τ.xi 0) = {x | x 0 - x 1 ≥ -2 ∧ x 1 ≥ 3})
    (hK₂ : realizationSet T h (τ.xi 1) = {x | x 0 - x 1 ≥ 0 ∧ 2 * x 0 + 3 * x 1 ≤ 25})
    (hK₃ : realizationSet T h (τ.xi 2) = {x | x 0 + x 1 ≤ 8 ∧ -x 0 + 3 * x 1 ≥ 0}) :
    feasibleSet τ.measure T h (3 / 4) =
        (realizationSet T h (τ.xi 0) ∩ realizationSet T h (τ.xi 1)) ∪
          (realizationSet T h (τ.xi 1) ∩ realizationSet T h (τ.xi 2)) ∧
      ¬ Convex ℝ (feasibleSet τ.measure T h (3 / 4)) := by sorry

end KallMayerSLP.ProbConstr
