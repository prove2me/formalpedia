-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_Supplement_theorem4_printed_false
-- name    : OfflinePolicyLearning.Trees.Supplement.theorem4_printed_false
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:14:27.371058+00:00
-- url     : https://prove2.me/theorems/a577ed62-c331-4338-a610-24045103ab60
-- title:
--   Theorem 4, p. 28 (corrected: the printed O_p regret rates for CAIPWL over depth-L trees are false — counterexample for every L, p)
-- statement:
--   Let $\mathcal X\subset\mathbb R^p$ be a bounded feature domain and $\Pi_L$ the class of depth-$L$ decision-tree policies on $\mathcal X$ (§6.1). The paper defines $X_n=O_p(a_n)$ by: for any $\epsilon>0$, with probability at least $1-\epsilon$, $|X_n/a_n|\le M$ for all $n\ge N$, for some $M>0$ and $N>0$ (p. 21).
--
--   Theorem 4 of the paper asserts: under Assumptions 1, 2, 3, the CAIPWL policy of Algorithm 1 over $\Pi_L$ satisfies
--   $$R(\hat\pi_{CAIPWL})=O_p\Big(\Big(\sqrt{(2^L-1)\log p+2^L\log d}+\tfrac43L^{1/4}\sqrt{2^L-1}\Big)\sqrt{\frac{V^*}{n}}\Big),$$
--   and in particular, for fixed $L,p,d$, $R(\hat\pi_{CAIPWL})=O_p\big(\sqrt{V^*/n}\big)$.
--
--   The statement is: **for every depth $L\ge1$ and dimension $p\ge1$, with $d=2$ actions, there is one instance violating both displayed conclusions**, each even in the weaker per-$n$ form "$\mathbf P(|X_n/a_n|>M)\le\epsilon$ for all $n\ge N$". The instance satisfies Assumptions 1, 2, 3, uses $K>1$ evenly sized folds and measurable estimators that are bounded, with propensity estimates bounded away from $0$, at each sample size.
--
--   For instance: the bounded domain $\mathcal X=\{0\}\subset\mathbb R^p$, on which every depth-$L$ tree is a constant policy, deterministic rewards $Y(a_1)=1$, $Y(a_2)=0$, uniform logging, $K=2$ alternating folds, $\hat e=1/2$ and $\hat\mu_a\equiv n$. Assumption 2 holds with zero product, $V^*=1$, and the inferior constant policy, of regret $1$, is selected with probability close to $1/2$, so $\sqrt n\,R(\hat\pi_{CAIPWL})$ is not bounded in probability.
--
--   The failure is inherited from Theorem 3: Assumption 2 bounds only the product of the two estimation errors. The covering results for trees (Lemma 4) are not affected and are the goal of this mission.
--
--   **Formalization Note** $\Pi_L$ on $\mathcal X$ is the base mission's `DTree` evaluation restricted to $\mathcal X$; the model and cross-fitting scheme are the published `Model` and `CrossFit`. Both conclusions are kept, with $d=2$ substituted in $2^L\log d$; the negated claim has their disjunction as conclusion, so one instance fails both. $|X_n/a_n|\le M$ is written literally with Lean's division ($a_n>0$ in the counterexample). The negated claim adds jointly measurable estimators, a bound on $|\hat\mu|$ and a positive lower bound on $\hat e$ at each sample size, and fold sizes between $\lfloor n/K\rfloor$ and $\lfloor n/K\rfloor+1$; each addition only strengthens the negation. The printed $O_p$ (one event for all $n\ge N$) implies the per-$n$ form, so refuting the latter refutes the printed theorem.
--
--   Differences from the source:
--   - correction: R(π̂) = O_p((√((2^L−1)log p + 2^L log d) + (4/3)L^{1/4}√(2^L−1))√(V*/n)) and R(π̂) = O_p(√(V*/n)) under Assumptions 1, 2, 3 → for every L ≥ 1, p ≥ 1 and d = 2, the negation of the claim that one of the two holds for every instance; reason: on X = {0} with deterministic rewards (1,0), uniform logging, ê = e and μ̂ ≡ n, Assumption 2 holds with zero product while the regret is 1 with probability near 1/2
--   - reading: O_p with one event for all n ≥ N → per-n bound P(|X_n/a_n| > M) ≤ ε for n ≥ N, in the negated claim; reason: the printed form implies the per-n form, so refuting the per-n form refutes the printed claim
--   - encoding: arbitrary estimators, evenly sized folds → jointly measurable estimators bounded (and ê bounded below by a positive constant) at each n, fold sizes ⌊n/K⌋ or ⌊n/K⌋ + 1, in the negated claim; reason: restricting the universally quantified claim strengthens its negation and keeps the integrals in Assumption 2 honest
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 28, Theorem 4; p. 27, §6 and §6.1 (bounded X ⊂ ℝ^p, depth-L trees); p. 21, definition of O_p; p. 12, Assumption 2; p. 14, Algorithm 1

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_OfflinePolicyLearning_Trees_Supplement_Setting

open MeasureTheory Filter Topology
open OfflinePolicyLearning.Regret

namespace OfflinePolicyLearning.Trees.Supplement

/-- Theorem 4, p. 28, as printed — under Assumptions 1, 2, 3, the CAIPWL policy over the
depth-`L` tree class on a bounded domain `X ⊂ ℝ^p` satisfies
`R(π̂) = O_p((√((2^L − 1) log p + 2^L log d) + (4/3) L^{1/4} √(2^L − 1)) √(V*/n))`, and in
particular `R(π̂) = O_p(√(V*/n))` — is false for every depth `L ≥ 1` and dimension `p ≥ 1`
(with `d = 2` actions): one instance violates both displayed conclusions. `O_p` is negated in its
weaker per-`n` form. The negated claim adds measurable estimators, a bound on `|μ̂|` and a
positive lower bound on `ê` at each sample size, and evenly sized folds. -/
theorem theorem4_printed_false (p L : ℕ) (hp : 1 ≤ p) (hL : 1 ≤ L) :
    ¬ ∀ (S : Set (Fin p → ℝ)) (M : Model S 2) (K : ℕ) (C : CrossFit S 2 K),
        Bornology.IsBounded S →
        (∃ η : ℝ, 0 < η ∧ ∀ x a, η ≤ M.e x a) →
        (∃ B : ℝ, ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) →
        1 < K →
        (∀ (n : ℕ) (k : Fin K),
          n / K ≤ (Finset.univ.filter fun i : Fin n => C.fold n i = k).card ∧
          (Finset.univ.filter fun i : Fin n => C.fold n i = k).card ≤ n / K + 1) →
        (∀ (n : ℕ) (k : Fin K) (a : Fin 2),
          Measurable fun q : ({i : Fin n // C.fold n i ≠ k} → Obs S 2) × S =>
            C.μhat n k q.1 q.2 a) →
        (∀ (n : ℕ) (k : Fin K) (a : Fin 2),
          Measurable fun q : ({i : Fin n // C.fold n i ≠ k} → Obs S 2) × S =>
            C.ehat n k q.1 q.2 a) →
        (∀ n : ℕ, ∃ b : ℝ, ∀ k T x a, |C.μhat n k T x a| ≤ b) →
        (∀ n : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ k T x a, c ≤ C.ehat n k T x a) →
        (∀ (k : Fin K) (a : Fin 2),
          Tendsto (fun n : ℕ => (n : ℝ) * (C.mseMu M n k a * C.mseE M n k a)) atTop (𝓝 0)) →
        (∃ Cc Dc ω : ℝ, 0 < Cc ∧ 0 < Dc ∧ 0 < ω ∧ ω < 1 / 2 ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            hammingCoverNum ε (treePoliciesOn p 2 L S) ≠ ⊤ ∧
            ((hammingCoverNum ε (treePoliciesOn p 2 L S)).toNat : ℝ) ≤
              Cc * Real.exp (Dc * (1 / ε) ^ ω)) →
        ∀ πh : (n : ℕ) → (Fin n → Draw S 2) → S → Fin 2,
          (∀ n D, πh n D ∈ treePoliciesOn p 2 L S) →
          (∀ n D, ∀ π ∈ treePoliciesOn p 2 L S, C.Qhat D π ≤ C.Qhat D (πh n D)) →
          (∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
            M.sample n {D | Mc < |M.regret (treePoliciesOn p 2 L S) (πh n D) /
              ((Real.sqrt ((2 ^ L - 1 : ℝ) * Real.log p + (2 : ℝ) ^ L * Real.log 2) +
                  4 / 3 * (L : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ L - 1 : ℝ)) *
                Real.sqrt (M.Vstar (treePoliciesOn p 2 L S) / n))|} ≤ ENNReal.ofReal ε) ∨
          (∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
            M.sample n {D | Mc < |M.regret (treePoliciesOn p 2 L S) (πh n D) /
                Real.sqrt (M.Vstar (treePoliciesOn p 2 L S) / n)|} ≤ ENNReal.ofReal ε) := by sorry

end OfflinePolicyLearning.Trees.Supplement
