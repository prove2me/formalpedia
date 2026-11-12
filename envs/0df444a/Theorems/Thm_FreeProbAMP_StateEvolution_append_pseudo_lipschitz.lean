-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_append_pseudo_lipschitz
-- name    : FreeProbAMP.StateEvolution.append_pseudo_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:10.385653+00:00
-- url     : https://prove2.me/theorems/427a126a-f46f-49fe-b2f8-bb5f3c6d448d
-- title:
--   Lemma 6.4 — append a pseudo-Lipschitz map
-- statement:
--   Suppose $X_i^d\in\mathbb R^q$, $i\le n(d)$, converges empirically to an all-moment random vector $X$, with positive $n(d)\to\infty$. Let $f:\mathbb R^q\to\mathbb R$ and its first partial derivatives be pseudo-Lipschitz of finite order. Then
--
--   $$(X_i^d,f(X_i^d))_{i\le n(d)}\xrightarrow{\rm emp}(X,f(X)),$$
--   $$\frac1{n(d)}\sum_i\partial_j f(X_i^d)\xrightarrow{\mathbb P}\mathbb E[\partial_j f(X)]\quad(1\le j\le q).$$
--
--   Every empirical polynomial moment of the enlarged tuple is $O_{\mathbb P}(1)$. The norm moments of every nonnegative integer order are explicitly tight. This supplies closure of empirical convergence under the smooth polynomial-growth maps used in AMP.
--
--   **Formalization Note** Continuous first partial derivatives imply $C^1$ regularity in finite dimension; their finitely many growth orders can be increased to one common finite order. The explicit smoothness predicate therefore adds no source instances restriction.
--
--   Differences from the source:
--   - reading: X is typed in R^q while f is typed in R^k before writing f(X) → one arbitrary input dimension q for the vector and the function; reason: resolves the incompatible dimension names without restricting the dimension
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
--   - encoding: f and ∂_1f, ..., ∂_kf pseudo-Lipschitz of finite order (1-based partials) → f is C¹ and f and every partial ∂_jf, j : Fin q (0-based), are pseudo-Lipschitz of one common order; reason: PL functions are continuous, so continuous partials give C¹; PL classes increase with the order, so finitely many orders can be replaced by their maximum; same instances
--   - encoding: all empirical polynomial moments are O_P(1) → for every p, the empirical mean of the p-th power of the Euclidean norm of the appended vector is tight; reason: every monomial is bounded by a power of 1 + the norm, and the even norm powers are polynomial moments; equivalent statements
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 30, Lemma 6.4

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 6.4, p.30; the source's q/k dimension names refer to one common dimension. -/
theorem append_pseudo_lipschitz
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ → ℕ) (q : ℕ) (hn : ∀ d, 0 < n d)
    (X : (d : ℕ) → Ω → Fin (n d) → Fin q → ℝ) (Y : E → Fin q → ℝ)
    (he : Empirical μ ν n X Y) (f : (Fin q → ℝ) → ℝ) (hf : SmoothPL f) :
    Empirical μ ν n (fun d ω i => append (X d ω i) (f (X d ω i)))
      (fun ξ => append (Y ξ) (f (Y ξ))) ∧
    (∀ j : Fin q, InProb μ (fun d ω => avg (n d) (fun i => derivCoord f j (X d ω i)))
      (∫ ξ, derivCoord f j (Y ξ) ∂ν)) ∧
    (∀ p : ℕ, Tight μ (fun d ω => avg (n d)
      (fun i => euclid (append (X d ω i) (f (X d ω i))) ^ p))) := by sorry

end FreeProbAMP.StateEvolution
