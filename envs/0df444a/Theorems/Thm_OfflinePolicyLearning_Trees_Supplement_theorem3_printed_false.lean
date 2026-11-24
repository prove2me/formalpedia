-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_Supplement_theorem3_printed_false
-- name    : OfflinePolicyLearning.Trees.Supplement.theorem3_printed_false
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:13:46.155894+00:00
-- url     : https://prove2.me/theorems/d21cfb6f-b96f-4a17-aca2-5337faf6e4fd
-- title:
--   Theorem 3, p. 22 (corrected: the printed CAIPWL regret bound under Assumptions 1, 2, 3 is false — counterexample)
-- statement:
--   Algorithm 1 (CAIPWL) splits the $n$ observations $(X_i,A_i,Y_i)$ into $K>1$ evenly sized folds; for each fold $k$ it builds estimators $\hat\mu^{-k}_a$, $\hat e^{-k}_a$ of $\mu_a$ and $e_a$ from the other folds only, forms the scores $\hat\Gamma_i=\frac{Y_i-\hat\mu^{-k(i)}_{A_i}(X_i)}{\hat e^{-k(i)}_{A_i}(X_i)}A_i+\hat\mu^{-k(i)}(X_i)$ and returns $\hat\pi\in\arg\max_{\pi\in\Pi}\frac1n\sum_i\langle\pi(X_i),\hat\Gamma_i\rangle$. Assumption 2 requires, for each action $a$ (and each fold),
--   $$\mathbf E\big[(\hat\mu^{(n)}_a(X)-\mu_a(X))^2\big]\cdot\mathbf E\big[(\hat e^{(n)}_a(X)-e_a(X))^2\big]=\frac{o(1)}n .$$
--
--   Theorem 3 of the paper asserts: under Assumptions 1, 2 and 3, for any $\delta>0$ there is an integer $N_\delta$ such that with probability at least $1-2\delta$ and for all $n\ge N_\delta$,
--   $$R(\hat\pi_{CAIPWL})\le\Big(54.4\sqrt2\,\kappa(\Pi)+435.2+\sqrt{2\log\tfrac1\delta}\Big)\sqrt{\frac{V^*}{n}} .$$
--
--   The statement is: **this claim is false, even in the weaker form where the bound is only required with probability at least $1-2\delta$ at each $n\ge N_\delta$ separately.** There is a model, a policy class, a cross-fitting scheme with measurable estimators (bounded, with propensity estimates bounded away from $0$, at each sample size) satisfying Assumptions 1, 2, 3, a selection of empirical maximizers and a $\delta>0$ for which no $N_\delta$ works.
--
--   For instance: one feature point, $d=2$, deterministic rewards $Y(a_1)=1$, $Y(a_2)=0$, uniform logging, the two constant policies, $K=2$ alternating folds, the exact propensity estimate $\hat e=1/2$ and the regression estimate $\hat\mu_a\equiv n$ for both actions at sample size $n$. The propensity error is zero, so the product in Assumption 2 is zero. The estimated value difference is $2n-4N_1+2N_1/n$ with $N_1\sim\mathrm{Bin}(n,1/2)$ the number of draws logging $a_1$, so the inferior constant policy is selected with probability close to $1/2$ and has regret $1$, while the bound tends to $0$; $\delta=1/8$ fails.
--
--   Assumption 2 constrains only the product of the two mean squared errors; the proof in Appendix E also uses rates for each error separately, bounded summands and control of the reciprocal propensity errors, which (3) does not supply. The pinned asymptotic form with those additional estimator hypotheses is the published Open goal `OfflinePolicyLearning.Regret.theorem3_caipwl_regret_Op`; it is a different theorem and is not restated here.
--
--   **Formalization Note** The model and cross-fitting scheme are the published `OfflinePolicyLearning.Regret.Model` and `CrossFit`; an estimator for fold $k$ is a function of the observed data outside fold $k$ only. The negated claim adds, as hypotheses of the universally quantified statement, measurable policies, jointly measurable estimators, a bound on $|\hat\mu|$ and a positive lower bound on $\hat e$ at each sample size, and fold sizes between $\lfloor n/K\rfloor$ and $\lfloor n/K\rfloor+1$; each such addition only strengthens the negation, and they keep the mean squared errors of Assumption 2 honest Bochner integrals. The printed common event over all $n\ge N_\delta$ implies the per-$n$ bound, so refuting the per-$n$ form refutes the printed one.
--
--   Differences from the source:
--   - correction: under Assumptions 1, 2, 3, with probability ≥ 1 − 2δ and for all n ≥ N_δ, R(π̂) ≤ (54.4√2κ + 435.2 + √(2 log(1/δ)))√(V*/n) → the negation of that claim (a counterexample exists); reason: with deterministic rewards (1,0), uniform logging, two constant policies, ê = e and μ̂ ≡ n, Assumption 2 holds with zero product while the inferior policy is chosen with probability near 1/2
--   - reading: one event for all n ≥ N_δ → the bound at each n ≥ N_δ with probability ≥ 1 − 2δ, in the negated claim; reason: the printed common event implies the per-n form, so refuting the per-n form refutes the printed claim
--   - encoding: Π any policy class, arbitrary estimators, evenly sized folds → measurable policies, jointly measurable estimators bounded (and ê bounded below by a positive constant) at each n, fold sizes ⌊n/K⌋ or ⌊n/K⌋ + 1, in the negated claim; reason: restricting the universally quantified claim strengthens its negation and keeps the integrals in Assumption 2 honest
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 22, Theorem 3; p. 12, Assumption 2 (3); p. 14, Algorithm 1; p. 11, §3 (cross-fitting); p. 9, Assumption 1; p. 14, Assumption 3; App. E

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory Filter Topology
open OfflinePolicyLearning.Regret

namespace OfflinePolicyLearning.Trees.Supplement

/-- Theorem 3, p. 22, as printed — under Assumptions 1, 2, 3, for the CAIPWL policy of
Algorithm 1 and any `δ > 0` there is `N_δ` such that with probability at least `1 − 2δ`, for all
`n ≥ N_δ`, `R(π̂) ≤ (54.4√2κ(Π) + 435.2 + √(2 log(1/δ)))√(V*/n)` — is false. The negated claim is
the weaker per-`n` form (the bound holds with probability `≥ 1 − 2δ` at each `n ≥ N_δ`, which the
printed common event implies) and adds measurable policies, measurable estimators, a bound on
`|μ̂|` and a positive lower bound on `ê` at each sample size, and evenly sized folds. -/
theorem theorem3_printed_false :
    ¬ ∀ (X : Type) [MeasurableSpace X] (d : ℕ) (M : Model X d) (Pol : Set (X → Fin d))
        (K : ℕ) (C : CrossFit X d K),
        Pol.Nonempty → (∀ π ∈ Pol, Measurable π) →
        (∃ η : ℝ, 0 < η ∧ ∀ x a, η ≤ M.e x a) →
        (∃ B : ℝ, ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) →
        1 < K →
        (∀ (n : ℕ) (k : Fin K),
          n / K ≤ (Finset.univ.filter fun i : Fin n => C.fold n i = k).card ∧
          (Finset.univ.filter fun i : Fin n => C.fold n i = k).card ≤ n / K + 1) →
        (∀ (n : ℕ) (k : Fin K) (a : Fin d),
          Measurable fun q : ({i : Fin n // C.fold n i ≠ k} → Obs X d) × X =>
            C.μhat n k q.1 q.2 a) →
        (∀ (n : ℕ) (k : Fin K) (a : Fin d),
          Measurable fun q : ({i : Fin n // C.fold n i ≠ k} → Obs X d) × X =>
            C.ehat n k q.1 q.2 a) →
        (∀ n : ℕ, ∃ b : ℝ, ∀ k T x a, |C.μhat n k T x a| ≤ b) →
        (∀ n : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ k T x a, c ≤ C.ehat n k T x a) →
        (∀ (k : Fin K) (a : Fin d),
          Tendsto (fun n : ℕ => (n : ℝ) * (C.mseMu M n k a * C.mseE M n k a)) atTop (𝓝 0)) →
        (∃ Cc Dc ω : ℝ, 0 < Cc ∧ 0 < Dc ∧ 0 < ω ∧ ω < 1 / 2 ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            hammingCoverNum ε Pol ≠ ⊤ ∧
            ((hammingCoverNum ε Pol).toNat : ℝ) ≤ Cc * Real.exp (Dc * (1 / ε) ^ ω)) →
        ∀ πh : (n : ℕ) → (Fin n → Draw X d) → X → Fin d,
          (∀ n D, πh n D ∈ Pol) →
          (∀ n D, ∀ π ∈ Pol, C.Qhat D π ≤ C.Qhat D (πh n D)) →
          ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N,
            ENNReal.ofReal (1 - 2 * δ) ≤ M.sample n {D | M.regret Pol (πh n D) ≤
              (54.4 * Real.sqrt 2 * (entropyIntegral Pol).toReal + 435.2 +
                  Real.sqrt (2 * Real.log (1 / δ))) * Real.sqrt (M.Vstar Pol / n)} := by sorry

end OfflinePolicyLearning.Trees.Supplement
