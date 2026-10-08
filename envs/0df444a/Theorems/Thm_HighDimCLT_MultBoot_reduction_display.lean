-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_reduction_display
-- name    : HighDimCLT.MultBoot.reduction_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:24.448254+00:00
-- url     : https://prove2.me/theorems/19c07990-003a-4054-93a9-4fa28b690584
-- title:
--   App. E.2, p. 2342 — |P(S^{eX}_n ∈ A | X₁ⁿ) − P(S^Y_n ∈ A)| ≤ Cϵ log^{1/2}(pn) + ρ̄ for a simple convex set A
-- statement:
--   Let $a,b,d>0$. There is $C>0$, depending only on $a,b,d$, such that the following holds. Assume the standing setting with $n\ge4$, $p\ge3$. Let $A\subseteq\mathbb R^p$ be a Borel set and $A^m=\bigcap_{v\in V}\{w:w'v\le s(v)\}$ a polyhedron given by a set $V$ of $m\le(pn)^d$ unit vectors, with $A^m\subseteq A\subseteq A^{m,\epsilon}$ for $\epsilon=a/n$ (condition (C)), and assume (M.1′): $n^{-1}\sum_i\mathrm E[(v'X_i)^2]\ge b$ for all $v\in V$. Then at every realization of the data,
--   $$\big|P(S_n^{eX}\in A\mid X_1^n)-P(S_n^Y\in A)\big|\le C\epsilon\log^{1/2}(pn)+\bar\rho,$$
--   where
--   $$\bar\rho=\max\Big\{\big|P(S_n^{eX}\in A^m\mid X_1^n)-P(S_n^Y\in A^m)\big|,\ \big|P(S_n^{eX}\in A^{m,\epsilon}\mid X_1^n)-P(S_n^Y\in A^{m,\epsilon})\big|\Big\}.$$
--
--   This reduces the bootstrap error at a simple convex set to the errors at two polyhedra, which are lower orthants for the $m$-dimensional vectors $(v'X_i)_{v\in V}$.
--
--   **Formalization Note** The page's $\mathcal V(A^m)$ consists of the facet normals of $A^m$ and $s(v)=\mathcal S_{A^m}(v)$; the statement allows any finite set of unit vectors with any thresholds, which covers the page's case. The page's second inequality, $C\epsilon\log^{1/2}(pn)=Cn^{-1}\log^{1/2}(pn)$ up to the constant, is the substitution $\epsilon=a/n$.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2342, App. E.2, Proof of Theorem 4.1, display after "As in the proof of Proposition 3.1"

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Reduction display**, App. E.2, p. 2342 (proof of Theorem 4.1): for one simple convex set
`A` with approximating polyhedron `A^m = ⋂_{v ∈ V} {w : w′v ≤ s(v)}` (`m ≤ (pn)^d` unit vectors,
`A^m ⊆ A ⊆ A^{m,ϵ}`, `ϵ = a/n`, and (M.1′)), at every realization of the data,
`|P(S^{eX}_n ∈ A | X₁ⁿ) − P(S^Y_n ∈ A)| ≤ C ϵ log^{1/2}(pn) + ρ̄`, where `ρ̄` is the larger of the
two bootstrap errors at `A^m` and at `A^{m,ϵ}`, and `C` depends only on `a, b, d`. -/
theorem reduction_display : ∀ a b d : ℝ, 0 < a → 0 < b → 0 < d → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n p : ℕ),
    4 ≤ n → 3 ≤ p → ∀ (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin p)), Standing P X Y →
    ∀ (A : Set (EuclideanSpace ℝ (Fin p))) (V : Finset (EuclideanSpace ℝ (Fin p)))
      (s : EuclideanSpace ℝ (Fin p) → ℝ),
    MeasurableSet A →
    (∀ v ∈ V, ‖v‖ = 1) →
    ((V.card : ℝ) ≤ ((p : ℝ) * n) ^ d) →
    (polyhedron V s ⊆ A ∧ A ⊆ enlarge V s (a / n)) →
    (∀ v ∈ V, b ≤ (∑ i, ∫ ω, inner ℝ v (X i ω) ^ 2 ∂P) / n) →
    ∀ ω : Ω,
      |(mbLaw (fun i => X i ω)).real A - P.real {ω' | normSum Y ω' ∈ A}|
        ≤ C * (a / n) * Real.sqrt (Real.log ((p : ℝ) * n))
          + max |(mbLaw (fun i => X i ω)).real (polyhedron V s)
                  - P.real {ω' | normSum Y ω' ∈ polyhedron V s}|
                |(mbLaw (fun i => X i ω)).real (enlarge V s (a / n))
                  - P.real {ω' | normSum Y ω' ∈ enlarge V s (a / n)}| := by sorry

end HighDimCLT.MultBoot
