-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Regret_theorem3_caipwl_regret_Op
-- name    : OfflinePolicyLearning.Regret.theorem3_caipwl_regret_Op
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:59.110458+00:00
-- url     : https://prove2.me/theorems/bd463b5e-905b-45ee-b281-9120d9128cf2
-- title:
--   Theorem 3 in the form of Remark 8, (18), p. 22 — R(π̂_CAIPWL) = O_p(κ(Π)√(V*/n))
-- statement:
--   Remark 8 (p. 22) states: "a simpler way of stating the regret bound in Theorem 3 is $R(\hat\pi_{CAIPWL})=O_p\big(\kappa(\Pi)\sqrt{V_*/n}\big)$". This theorem is that statement.
--
--   Work in the potential-outcome model of the mission: $n$ iid draws of features $X$, potential outcomes $(Y(1),\dots,Y(d))$ and a logged action $A$, with $Y\perp A\mid X$ (Assumption 1.1, built into the model). Let $\hat\pi_{CAIPWL}$ be any maximizer over $\Pi$ of the cross-fitted AIPW value estimate $\hat Q_{CAIPWL}(\pi)=\frac1n\sum_i\langle\pi(X_i),\hat\Gamma_i\rangle$ (Algorithm 1). Assume:
--
--   1. Assumption 1: overlap $e_a(x)\ge\eta>0$ and bounded rewards $|Y(a)|\le B$;
--   2. $K\ge2$ evenly sized folds (each fold has at least $\lfloor n/K\rfloor$ points);
--   3. Assumption 2: $n\cdot\mathbb E[(\hat\mu^{-k}_a(X)-\mu_a(X))^2]\cdot\mathbb E[(\hat e^{-k}_a(X)-e_a(X))^2]\to0$ for every fold $k$ and action $a$;
--   4. (pinned) both mean-squared errors tend to $0$; the estimators are bounded, $|\hat\mu^{-k}_a|\le\hat B$, $\hat e^{-k}_a\ge\hat\eta>0$, and measurable;
--   5. $\Pi$ nonempty, its policies measurable, the class permissible;
--   6. Assumption 3: for $0<\varepsilon<1$, $N_H(\varepsilon,\Pi)<\infty$ and $N_H(\varepsilon,\Pi)\le C\exp(D(1/\varepsilon)^\omega)$ with $C,D>0$, $0<\omega<1/2$.
--
--   Then
--   $$R(\hat\pi_{CAIPWL})=O_p\Big(\kappa(\Pi)\sqrt{\frac{V_*}{n}}\Big):$$
--   for every $\varepsilon>0$ there exist $M>0$ and $N$ such that for all $n\ge N$,
--   $$\mathbb P\Big(R(\hat\pi_{CAIPWL})>M\,\kappa(\Pi)\sqrt{V_*/n}\Big)\le\varepsilon.$$
--
--   The rate is that of an oracle knowing the nuisance functions, obtained although each nuisance estimate may converge more slowly than $n^{-1/2}$.
--
--   **Formalization Note** The explicit-constant display of Theorem 3, $R(\hat\pi_{CAIPWL})\le(54.4\sqrt2\kappa(\Pi)+435.2+\sqrt{2\log(1/\delta)})\sqrt{V_*/n}$, is not posed: it rests on Theorem 1 and Lemma 2, whose constants are not established (the false Lemma 1(2), the failing $\sqrt{V_*}$ scaling, the arithmetic slip $435.2$ for $435.2\sqrt2$, and $o$-terms that cannot be absorbed at a fixed probability). The pins in item 4 and permissibility are added for the reasons given at Lemma 3. $O_p$ is read for each $n$ separately. $\kappa(\Pi)$ is finite under Assumption 3, so its real value is used. The degenerate cases are covered: if $\kappa(\Pi)=0$ or $V_*=0$, all policies of $\Pi$ have the same value and the regret is $0$.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 22, Theorem 3 and Remark 8, display (18); Assumptions 1–3, pp. 9, 12, 14; Algorithm 1, p. 14

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace OfflinePolicyLearning.Regret
theorem theorem3_caipwl_regret_Op {X : Type*} [MeasurableSpace X] {d : ℕ}
    (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (K : ℕ) (hK : 2 ≤ K) (C : CrossFit X d K)
    (hfold : ∀ (n : ℕ) (k : Fin K), n / K ≤ (Finset.univ.filter fun i : Fin n => C.fold n i = k).card)
    (h2 : ∀ (k : Fin K) (a : Fin d),
      Tendsto (fun n : ℕ => (n : ℝ) * (C.mseMu M n k a * C.mseE M n k a)) atTop (𝓝 0))
    (h2μ : ∀ (k : Fin K) (a : Fin d), Tendsto (fun n : ℕ => C.mseMu M n k a) atTop (𝓝 0))
    (h2e : ∀ (k : Fin K) (a : Fin d), Tendsto (fun n : ℕ => C.mseE M n k a) atTop (𝓝 0))
    (Bhat ηhat : ℝ) (hηhat : 0 < ηhat)
    (hμbdd : ∀ n k T x a, |C.μhat n k T x a| ≤ Bhat)
    (hebdd : ∀ n k T x a, ηhat ≤ C.ehat n k T x a)
    (hμmeas : ∀ (n : ℕ) (k : Fin K) (a : Fin d),
      Measurable fun p : ({i : Fin n // C.fold n i ≠ k} → Obs X d) × X => C.μhat n k p.1 p.2 a)
    (hemeas : ∀ (n : ℕ) (k : Fin K) (a : Fin d),
      Measurable fun p : ({i : Fin n // C.fold n i ≠ k} → Obs X d) × X => C.ehat n k p.1 p.2 a)
    (Pol : Set (X → Fin d)) (hPol : Pol.Nonempty) (hPmeas : ∀ π ∈ Pol, Measurable π)
    (hperm : ∀ (m : ℕ) (s : Fin m → Fin d),
      MeasurableSet {x : Fin m → X | ∃ π ∈ Pol, ∀ i, π (x i) = s i})
    (Cc Dc ω : ℝ) (hCc : 0 < Cc) (hDc : 0 < Dc) (hω : 0 < ω) (hω' : ω < 1 / 2)
    (h3 : ∀ ε : ℝ, 0 < ε → ε < 1 → hammingCoverNum ε Pol ≠ ⊤ ∧
      ((hammingCoverNum ε Pol).toNat : ℝ) ≤ Cc * Real.exp (Dc * (1 / ε) ^ ω))
    (πhat : (n : ℕ) → (Fin n → Draw X d) → X → Fin d)
    (hmem : ∀ n D, πhat n D ∈ Pol)
    (hmax : ∀ n D, ∀ π ∈ Pol, C.Qhat D π ≤ C.Qhat D (πhat n D)) :
    ∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
      M.sample n {D | Mc * (entropyIntegral Pol).toReal * Real.sqrt (M.Vstar Pol / n) <
        M.regret Pol (πhat n D)} ≤ ENNReal.ofReal ε := by sorry
end OfflinePolicyLearning.Regret
