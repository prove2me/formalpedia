-- Prove2me | Theorems.Thm_KallMayerSLP_CondExp_proposition_1_3
-- name    : KallMayerSLP.CondExp.proposition_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:30.864995+00:00
-- url     : https://prove2.me/theorems/e1639645-8bb7-4d35-9e7e-c26fa8c6951f
-- title:
--   Proposition 1.3 — log-concavity via concavity of $\log f$ on the positivity set
-- statement:
--   Let $C\subseteq\mathbb R^n$ be convex and $f:C\to\mathbb R$ nonnegative, and write $C^+=\{x\in C\mid f(x)>0\}$. Then $f$ is log-concave over $C$, meaning
--   $$
--   f(\lambda x+(1-\lambda)y)\ge f(x)^\lambda f(y)^{1-\lambda}\qquad(x,y\in C,\ \lambda\in(0,1)),
--   $$
--   if and only if $C^+$ is convex and $\log f$ is concave over $C^+$.
--
--   This passes between the power form, which allows zeros, and ordinary concavity on the set where $f$ is positive.
--
--   Differences from the source:
--   - encoding: Definition 1.3 with λ ∈ (0, 1) → the published LogConcaveOn, with weights a, b ≥ 0, a + b = 1; reason: the endpoint weights a = 0, b = 1 and a = 1, b = 0 are trivially true, so the two definitions agree on a convex set
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 1.3, p.90

import Mathlib
import Definitions.Def_LogConcaveOn

namespace KallMayerSLP.CondExp

/-- Characterization of log-concavity: a nonnegative `f` is log-concave over the convex set `C` iff
`C⁺ = {x ∈ C | f x > 0}` is convex and `log f` is concave over `C⁺`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Proposition 1.3, p.90 (PDF 100).

**Formalization Note** Definition 1.3 is the published `ConvexOptimization.LogConcaveOn`, whose
weights `a, b ≥ 0`, `a + b = 1` add only the trivial endpoints to the book's `λ ∈ (0, 1)`. -/
theorem proposition_1_3 {n : ℕ} (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ x ∈ C, 0 ≤ f x) :
    ConvexOptimization.LogConcaveOn C f ↔
      Convex ℝ {x | x ∈ C ∧ 0 < f x} ∧
        ConcaveOn ℝ {x | x ∈ C ∧ 0 < f x} (fun x => Real.log (f x)) := by sorry

end KallMayerSLP.CondExp
