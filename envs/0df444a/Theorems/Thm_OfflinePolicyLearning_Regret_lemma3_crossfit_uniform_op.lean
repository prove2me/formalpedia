-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Regret_lemma3_crossfit_uniform_op
-- name    : OfflinePolicyLearning.Regret.lemma3_crossfit_uniform_op
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:51.802217+00:00
-- url     : https://prove2.me/theorems/376455c1-fcbe-4153-9745-f7728fa225ee
-- title:
--   Lemma 3, p. 21 (pinned: Assumption 2 strengthened) — sup_{π₁,π₂∈Π} |Δ̂(π₁,π₂) − Δ̃(π₁,π₂)| = o_p(1/√n)
-- statement:
--   Work in the potential-outcome model of the mission with cross-fitting over $K\ge2$ evenly sized folds (every fold of a sample of size $n$ has at least $\lfloor n/K\rfloor$ points). Assume:
--
--   1. overlap $e_a(x)\ge\eta>0$ and bounded rewards $|Y(a)|\le B$ (Assumption 1; unconfoundedness is built into the model);
--   2. Assumption 2: for every fold $k$ and action $a$, $n\cdot\mathbb E[(\hat\mu^{-k}_a(X)-\mu_a(X))^2]\cdot\mathbb E[(\hat e^{-k}_a(X)-e_a(X))^2]\to0$;
--   3. (pinned) both mean-squared errors tend to $0$ separately;
--   4. (pinned) the estimators are bounded, $|\hat\mu^{-k}_a(x)|\le\hat B$ and $\hat e^{-k}_a(x)\ge\hat\eta>0$, and jointly measurable in (training data, $x$);
--   5. $\Pi$ is nonempty, its policies are measurable, and for every $m$ and action pattern $s$ the set of point sequences $(x_1,\dots,x_m)$ on which some $\pi\in\Pi$ realizes $s$ is measurable;
--   6. $\kappa(\Pi)<\infty$.
--
--   Then
--   $$\sup_{\pi_1,\pi_2\in\Pi}\big|\hat\Delta(\pi_1,\pi_2)-\tilde\Delta(\pi_1,\pi_2)\big|=o_p\Big(\frac1{\sqrt n}\Big),$$
--   that is, for every $\varepsilon>0$, $\ \mathbb P\big(\exists\,\pi_1,\pi_2\in\Pi:\ |\hat\Delta(\pi_1,\pi_2)-\tilde\Delta(\pi_1,\pi_2)|\ge\varepsilon/\sqrt n\big)\to0$.
--
--   This is the step at which cross-fitting pays off: the feasible doubly robust value differences are uniformly within $o_p(n^{-1/2})$ of the oracle ones, even when each nuisance estimate converges slower than $n^{-1/2}$.
--
--   **Formalization Note** Items 3–4 and the permissibility condition in 5 are added to the printed hypotheses. The paper's proof (App. E, pp. 63–67) uses separate rates for the two nuisance errors and bounds $1/\hat e-1/e$ by $|\hat e-e|$, which needs $\hat e$ bounded away from $0$; without consistency of $\hat\mu$ the printed statement fails ($\hat\mu\equiv0$, $\hat e=e$ satisfies (3), and the first term of (17) is then of exact order $n^{-1/2}$). Permissibility makes the suprema over $\Pi$ random variables, which the paper takes for granted. The event "supremum $\ge t$" is written as "some pair has $|\cdot|\ge t$"; they coincide because both $\hat\Delta$ and $\tilde\Delta$ take finitely many values on a given sample. The mean-squared errors are of the estimators actually used at sample size $n$.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 21, Lemma 3; o_p of Definition 8 item 2, p. 21; Assumption 2 (3), p. 12; proof App. E, pp. 63–67

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace OfflinePolicyLearning.Regret
theorem lemma3_crossfit_uniform_op {X : Type*} [MeasurableSpace X] {d : ℕ}
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
    (hκ : entropyIntegral Pol ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => M.sample n {D | ∃ πa ∈ Pol, ∃ πb ∈ Pol,
        ε / Real.sqrt n ≤ |C.Δhat D πa πb - M.Δtilde D πa πb|}) atTop (𝓝 0) := by sorry
end OfflinePolicyLearning.Regret
