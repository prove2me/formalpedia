-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_theorem_2
-- name    : OptimalAgnosticPAC.Learner.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:22.766926+00:00
-- url     : https://prove2.me/theorems/2ffe961e-defc-4f61-bf22-db56616fe8ed
-- title:
--   Theorem 2: orientation of the cube and the leave-one-out bound
-- statement:
--   Let $d\ge1$.
--
--   1. Let $P$ be a nonempty finite coordinate set and let $\emptyset\ne\mathcal F\subseteq V_P$ satisfy $\mathrm{VC}(\mathcal F)\le d$. There is an orientation $\sigma$ of the full cube such that, for every $v\in V_P$,
--   $$\mathrm{out}(v;\sigma)\le\rho_{\mathcal F}(v)+120\sqrt{d\rho_{\mathcal F}(v)}+7202d.\tag{11}$$
--   2. Let $\mathcal H$ be a class of VC dimension at most $d$. For every $n\ge1$ and every input sequence $x_1,\dots,x_n$, allowing repetitions, there is a leave-one-out rule depending only on the unlabeled sequence such that, for every $(y_1,\dots,y_n)\in\{-1,+1\}^n$,
--   $$\widehat L^{\mathrm{LOO}}_S\le\widehat L^*_S+120\sqrt{\frac{d\widehat L^*_S}{n}}+7202\frac dn.\tag{12}$$
--
--   This is the optimal agnostic leave-one-out bound. The coefficient on $\widehat L^*_S$ is exactly one.
--
--   Differences from the source:
--   - encoding: V_P = {−1,+1}^P with P a nonempty finite set → P : Type with Fintype and Nonempty, labelings P → Bool with true for +1, signed values through sgn; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - encoding: labels in {−1,+1}, inputs in a set X → labels in Bool with true for +1, signed values through sgn, X : Type; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - encoding: an orientation chooses a head σ(e) ∈ e for each edge → a total map σ : Sym2 V → V with σ e ∈ e on the edge set; reason: values off the edge set are never read
--   - encoding: a leave-one-out rule depending only on the unlabeled sequence → rule : Fin n → (Fin n → Bool) → Bool, chosen after x and before y, whose value at i ignores y i; reason: the same prediction map; a function is deterministic and need not come from H
--   - generalization: H is a measurable class with VC(H) = d ≥ 1 → H is nonempty with vcDim H ≤ d, with no measurability; reason: part 2 is combinatorial and the bound is increasing in d, so d = VC(H) gives the source's statement
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §2, Theorem 2, PDF p. 6 (printed p. 5)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Risk
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Theorem 2, PDF p. 6. First part: the orientation of the full cube with bound (11). Second
part: for every input sequence, one leave-one-out rule, chosen from the inputs alone, with bound
(12) for every label vector. -/
theorem theorem_2 (d : ℕ) (hd : 1 ≤ d) :
    (∀ (P : Type) [Fintype P] [Nonempty P] (F : Set (P → Bool)), F.Nonempty →
      HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞) →
      ∃ σ : Sym2 (P → Bool) → (P → Bool), IsOrientation (cubeGraph P) σ ∧
        ∀ v : P → Bool, (outdegree (cubeGraph P) σ v : ℝ) ≤
          (rho F v : ℝ) + 120 * Real.sqrt ((d : ℝ) * (rho F v : ℝ)) + 7202 * (d : ℝ)) ∧
    (∀ (X : Type) (H : Set (X → Bool)), H.Nonempty →
      HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞) →
      ∀ (n : ℕ), 1 ≤ n → ∀ x : Fin n → X,
      ∃ rule : Fin n → (Fin n → Bool) → Bool, IsLOORule rule ∧
        ∀ y : Fin n → Bool,
          looRisk rule y ≤
            empMinRisk H (fun i => (x i, y i)) +
              120 * Real.sqrt ((d : ℝ) * empMinRisk H (fun i => (x i, y i)) / (n : ℝ)) +
              7202 * ((d : ℝ) / (n : ℝ))) := by sorry

end OptimalAgnosticPAC.Learner
