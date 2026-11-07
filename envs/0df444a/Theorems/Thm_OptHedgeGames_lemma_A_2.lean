-- Prove2me | Theorems.Thm_OptHedgeGames_lemma_A_2
-- name    : OptHedgeGames.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:39:33.891725+00:00
-- url     : https://prove2.me/theorems/cca36c18-16e7-458d-b3b7-fe8d49762b26
-- title:
--   Lemma A.2 — exponential tilting: density, variance, movement, Lipschitz and KL bounds
-- statement:
--   Let $p\in\Delta_n$, let $z\in\mathbb R^n$ with $\mathrm{osc}(z)\le r$, and let $q=E_p[z]$. Then:
--
--   1. $e^{-r}\le q(a)/p(a)\le e^r$ for every $a$ in the support of $p$;
--   2. $e^{-r}\mathrm{Var}_p(w)\le\mathrm{Var}_q(w)\le e^r\mathrm{Var}_p(w)$ for every $w\in\mathbb R^n$;
--   3. $\|E_p[z]-p\|_1\le e^{r/2}\|z\|_p$;
--   4. $\|E_p[z]-E_p[w]\|_1\le\|z-w\|_\infty$ for every $w\in\mathbb R^n$;
--   5. $\tfrac12e^{-r}\mathrm{Var}_p(z)\le\mathrm{KL}(p\|E_p[z])\le\tfrac12e^r\mathrm{Var}_p(z)$.
--
--   Since an Optimistic Hedge update is an exponential tilt, these bounds control how far one update moves a strategy.
--
--   Differences from the source: none.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Lemma A.2, pp.43–44

import Mathlib
import Definitions.Def_OptHedgeGames_Notation

namespace OptHedgeGames

/-- **Lemma A.2** (exponential tilting; Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Lemma A.2, pp.43–44). Let `p ∈ Δₙ`, let `z ∈ ℝⁿ` with
`osc(z) ≤ r`, and let `q = E_p[z]`. Then:
(i) `e⁻ʳ ≤ q(a)/p(a) ≤ eʳ` for every `a` in the support of `p`;
(ii) `e⁻ʳ Var_p(w) ≤ Var_q(w) ≤ eʳ Var_p(w)` for every `w ∈ ℝⁿ`;
(iii) `∥E_p[z] − p∥₁ ≤ e^{r/2}∥z∥_p`;
(iv) `∥E_p[z] − E_p[w]∥₁ ≤ ∥z − w∥_∞` for every `w ∈ ℝⁿ`;
(v) `½e⁻ʳ Var_p(z) ≤ KL(p ∥ E_p[z]) ≤ ½eʳ Var_p(z)`.

**Formalization Note** `p` may have zero entries, hence the support condition in (i). The real
quotient `q(a)/p(a)` is read only where `p(a) > 0`. `r ≥ 0` is forced by `osc z ≤ r`. -/
theorem lemma_A_2 {n : ℕ} (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (z : Fin n → ℝ) (r : ℝ)
    (hr : osc z ≤ r) :
    (∀ a, 0 < p a → Real.exp (-r) ≤ tilt p z a / p a ∧ tilt p z a / p a ≤ Real.exp r) ∧
      (∀ w : Fin n → ℝ, Real.exp (-r) * var p w ≤ var (tilt p z) w ∧
        var (tilt p z) w ≤ Real.exp r * var p w) ∧
      l1Norm (tilt p z - p) ≤ Real.exp (r / 2) * vnorm p z ∧
      (∀ w : Fin n → ℝ, l1Norm (tilt p z - tilt p w) ≤ ‖z - w‖) ∧
      (1 / 2 * Real.exp (-r) * var p z ≤ kl p (tilt p z) ∧
        kl p (tilt p z) ≤ 1 / 2 * Real.exp r * var p z) := by sorry

end OptHedgeGames
