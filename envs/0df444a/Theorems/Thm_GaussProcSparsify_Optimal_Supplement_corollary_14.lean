-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_corollary_14
-- name    : GaussProcSparsify.Optimal.Supplement.corollary_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:22:41.896972+00:00
-- url     : https://prove2.me/theorems/547b2f55-7968-4680-9460-99c270b7d727
-- title:
--   Corollary 14 — shifted and centered Lᵖ sparsification
-- statement:
--   There is a universal constant $C>0$ such that, for every dimension $n$, finite real $p\ge2$, $0<\alpha<1$, and nonempty bounded $T\subseteq\mathbb R^n$, both conclusions hold:
--
--   1. There are a finite nonempty $S\subseteq T$ and nonnegative shifts $c_s$ with
--   $$|S|\le e^{Cp/\alpha^2},\qquad\|\sup_{t\in T}\langle g,t\rangle-\max_{s\in S}(\langle g,s\rangle+c_s)\|_{L^p(\gamma_n)}\le\alpha w(T).$$
--   2. There are $m\ge n$ and a finite nonempty $U\subseteq\mathbb R^m$ with
--   $$|U|\le e^{Cp/\alpha^2},\qquad\|\sup_{t\in T}\langle g,(t,0_{m-n})\rangle-\sup_{u\in U}\langle g,u\rangle\|_{L^p(\gamma_m)}\le\alpha w(T).$$
--   The second clause permits new centered directions in a larger Gaussian space. Together these provide the support for the norm-junta and halfspace approximation theorems.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: bounded T and finite S in expressions involving sup and max → T.Nonempty and S.Nonempty with S a Finset; reason: excludes only undefined empty suprema and maxima, without restricting T to be finite
--   - encoding: Lᵖ error with finite real p≥2 → eLpNorm at ENNReal.ofReal p, compared to ENNReal.ofReal of the stated bound; reason: all source exponents are retained, and a divergent norm cannot satisfy a finite bound
--   - encoding: finite Gaussian width w(T) of nonempty bounded T → the published EReal Gaussian width converted to real on this domain; reason: bounded nonempty T has finite width, so conversion preserves its value, including width zero
--   - encoding: universal constants in asymptotic notation → positive existential constants before all instance parameters; reason: spells out the uniformity of the source bounds without selecting a numerical constant
--   - encoding: a set U with finite cardinality bound in the larger space → a nonempty Finset U with its maximum written as shiftedMax with zero shifts; reason: finite nonempty suprema equal maxima, and zeroPad implements exactly the stated embedding
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Corollary 14, PDF p. 22 (printed p. 21), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Supplement_Approximation

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Corollary 14, PDF pp. 22–23: both the shifted original-space and centered
larger-space clauses, with a single universal size constant. -/
theorem corollary_14 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (p α : ℝ) (T : Set (Vec n)), 2 ≤ p → 0 < α → α < 1 →
      T.Nonempty → Bornology.IsBounded T →
      (∃ (S : Finset (Vec n)) (hS : S.Nonempty) (c : Vec n → ℝ),
        (↑S : Set (Vec n)) ⊆ T ∧ (∀ s ∈ S, 0 ≤ c s) ∧
          (S.card : ℝ) ≤ Real.exp (C * p / α ^ 2) ∧
          eLpNorm (fun g => processSup T g - shiftedMax S hS c g)
            (ENNReal.ofReal p) (gaussian n) ≤ ENNReal.ofReal (α * (gaussianWidth T).toReal)) ∧
      (∃ m : ℕ, n ≤ m ∧ ∃ U : Finset (Vec m), ∃ hU : U.Nonempty,
        (U.card : ℝ) ≤ Real.exp (C * p / α ^ 2) ∧
          eLpNorm (fun g => processSup (zeroPad (m := m) '' T) g -
            shiftedMax U hU (fun _ => 0) g) (ENNReal.ofReal p) (gaussian m) ≤
              ENNReal.ofReal (α * (gaussianWidth T).toReal)) := by sorry

end GaussProcSparsify.Optimal.Supplement
