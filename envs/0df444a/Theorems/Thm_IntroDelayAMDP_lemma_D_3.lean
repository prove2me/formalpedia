-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_D_3
-- name    : IntroDelayAMDP.lemma_D_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T05:44:16.820567+00:00
-- url     : https://prove2.me/theorems/bebd0c7f-ff60-47c5-a01b-c725ec86abb5
-- title:
--   Lemma D.3 — stability of exponential weights
-- statement:
--   Let $A'$ be a finite set, $\pi\in\Delta(A')$ with $\pi>0$, $g:A'\to\mathbb R$, $\eta>0$ and $\pi'(a)\propto\pi(a)e^{-\eta g(a)}$. Then every $a\in A'$ satisfies
--   $$\Bigl|\log\frac{\pi'(a)}{\pi(a)}\Bigr|\le\eta\bigl(\max_{a'}g(a')-\min_{a'}g(a')\bigr).$$
--   It controls how far one exponential-weights update moves the policy.
--
--   Differences from the source:
--   - encoding: A′ a finite set with π ∈ ∆(A′) → A′ a finite nonempty type; reason: nonempty because ∆(A′) is nonempty
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma D.3, p.66

import Mathlib

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma D.3 (Stability of Exponential Weights)** (printed p.66, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "Let `A′` be a finite
set, `π ∈ ∆(A′)` with `π > 0`, `g : A′ → ℝ`, `η > 0`, and `π′(a) ∝ π(a)e^{−ηg(a)}`. Then every `a ∈ A′`
satisfies `|log(π′(a)/π(a))| ≤ η(max_{a′} g(a′) − min_{a′} g(a′))`."

**Formalization Note.** `A′` is a finite nonempty type (nonempty because `π ∈ ∆(A′)`); the maximum and
minimum are `Finset.sup'`/`Finset.inf'` over all of `A′`; `log` is natural. -/
theorem lemma_D_3 {A' : Type} [Fintype A'] [Nonempty A'] (π : A' → ℝ) (hπ : ∀ a, 0 < π a)
    (hπ1 : ∑ a, π a = 1) (g : A' → ℝ) (η : ℝ) (hη : 0 < η) (π' : A' → ℝ)
    (hπ' : ∀ a, π' a = π a * Real.exp (-η * g a) / ∑ b, π b * Real.exp (-η * g b)) (a : A') :
    |Real.log (π' a / π a)| ≤
      η * (Finset.univ.sup' Finset.univ_nonempty g - Finset.univ.inf' Finset.univ_nonempty g) := by sorry

end IntroDelayAMDP
