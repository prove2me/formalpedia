-- Prove2me | Theorems.Thm_KellyStochasticNetworks_CountableReversal_stationary_time_reversal
-- name    : KellyStochasticNetworks.CountableReversal.stationary_time_reversal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:49.675683+00:00
-- url     : https://prove2.me/theorems/44b4bf10-d536-42c2-96d9-bb3a04e5bb51
-- title:
--   Proposition 1.1 — stationary time reversal on countable state spaces
-- statement:
--   Let $S$ be a nonempty countable discrete measurable state space and $(X(t),t\in\mathbb R)$ an irreducible stationary Markov process on a probability space with jump rates $q(j,k)$ and equilibrium distribution $\pi$. The standing assumptions are $q(j,k)\ge0$, $q(j,j)=0$, positive finite exit rates $q(j)=\sum_kq(j,k)$, and nonexplosive piecewise constant paths with positive holding intervals. The equilibrium masses are strictly positive, sum to one, satisfy the convergent equilibrium equations, and give the law of $X(t)$ at every time. Off-diagonal rates are the right-hand small-time conditional-probability limits.
--
--   Define the actual reversed process by $Y(t)=X(-t)$. Then $Y$ is again a stationary Markov process with the same equilibrium distribution and with rates
--   $$
--   q'(j,k)=\frac{\pi(k)q(k,j)}{\pi(j)}\quad(j,k\in S).
--   $$
--   In particular its one-time law is $\pi$, its finite-dimensional distributions are invariant under time translations, and for $j\ne k$,
--   $$
--   \lim_{h\downarrow0}\frac{P(Y(t+h)=k\mid Y(t)=j)}h=q'(j,k).
--   $$
--   The reversed rates are nonnegative with zero diagonal, positive finite exit rates, irreducible communication, and the same convergent equilibrium equations. This is a statement about the reversed stochastic process, not merely its rate matrix.
--
--   **Formalization Note** Markovianity is defined by finite-history conditional laws, not by past–future independence. All process predicates are explicit local abbreviations in the theorem, so no unpublished model is imported. Nonexplosion is represented by finitely many possible changes on every bounded interval and positive constant intervals on either side of each time. At a jump the value is either adjoining state: time reversal exchanges the right-continuous and left-continuous conventions, without changing any fixed-time distributions. Stationarity is stated for all finite-dimensional distributions. All real infinite sums have summability or `HasSum` guards. No global finite stationary jump intensity is assumed.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 16–17 (PDF pp. 24–25), Proposition 1.1; standing assumptions printed pp. 13–15 (PDF pp. 21–23); https://doi.org/10.1017/CBO9781139565363

import Mathlib

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace KellyStochasticNetworks.CountableReversal

theorem stationary_time_reversal {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [Nonempty S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → S) (q : S → S → ℝ) (π : S → ℝ) :
    let cp := fun (A B : Set Ω) => (P (A ∩ B)).toReal / (P B).toReal
    let cylinder := fun (Z : ℝ → Ω → S) (n : ℕ)
      (t : Fin n → ℝ) (x : Fin n → S) => {ω | ∀ i, Z (t i) ω = x i}
    let markov := fun (Z : ℝ → Ω → S) =>
      ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
        StrictMono t → (∀ i, t i < s) → s < u →
        0 < (P (cylinder Z n t x ∩ {ω | Z s ω = j})).toReal →
        cp {ω | Z u ω = k} (cylinder Z n t x ∩ {ω | Z s ω = j}) =
          cp {ω | Z u ω = k} {ω | Z s ω = j}
    let stationary := fun (Z : ℝ → Ω → S) =>
      ∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (h : ℝ),
        P (cylinder Z n (fun i => t i + h) x) = P (cylinder Z n t x)
    let regular := fun (Z : ℝ → Ω → S) =>
      ∀ᵐ ω ∂P,
        (∀ a b : ℝ, ∃ D : Finset ℝ,
          ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
            (∀ u ∈ D, u ∉ Icc s t) → Z s ω = Z t ω) ∧
        (∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∃ l r : S,
          (∀ s ∈ Ioo (t - ε) t, Z s ω = l) ∧
          (∀ s ∈ Ioo t (t + ε), Z s ω = r) ∧
          (Z t ω = l ∨ Z t ω = r))
    let rateData := fun (Q : S → S → ℝ) =>
      (∀ j k, 0 ≤ Q j k) ∧ (∀ j, Q j j = 0) ∧
      (∀ j, Summable (Q j)) ∧ (∀ j, 0 < ∑' k, Q j k) ∧
      (∀ j k, Relation.ReflTransGen (fun a b => 0 < Q a b) j k)
    let equilibrium := fun (Q : S → S → ℝ) =>
      (∀ j, 0 < π j) ∧ HasSum π 1 ∧
        (∀ j, HasSum (fun k => π k * Q k j) (π j * ∑' k, Q j k))
    let rates := fun (Z : ℝ → Ω → S) (Q : S → S → ℝ) =>
      ∀ (t : ℝ) (j k : S), j ≠ k →
        Tendsto (fun h : ℝ => cp {ω | Z (t + h) ω = k} {ω | Z t ω = j} / h)
          (𝓝[>] (0 : ℝ)) (𝓝 (Q j k))
    let Y := fun t ω => X (-t) ω
    let q' := fun j k => π k * q k j / π j
    (∀ t, Measurable (X t)) → regular X → markov X → stationary X →
      rateData q → equilibrium q →
      (∀ t j, (P {ω | X t ω = j}).toReal = π j) → rates X q →
    (∀ t, Measurable (Y t)) ∧ regular Y ∧ markov Y ∧ stationary Y ∧
      rateData q' ∧ equilibrium q' ∧
      (∀ t j, (P {ω | Y t ω = j}).toReal = π j) ∧ rates Y q' := by sorry

end KellyStochasticNetworks.CountableReversal
