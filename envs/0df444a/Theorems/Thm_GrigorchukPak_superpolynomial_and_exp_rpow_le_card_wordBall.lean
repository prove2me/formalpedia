-- Prove2me | Theorems.Thm_GrigorchukPak_superpolynomial_and_exp_rpow_le_card_wordBall
-- name    : GrigorchukPak.superpolynomial_and_exp_rpow_le_card_wordBall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T14:24:24.386083+00:00
-- url     : https://prove2.me/theorems/9b27e0ad-e2d0-469c-8d88-e9d3f2e62f22
-- title:
--   Grigorchuk–Pak, Corollary 6.5 — the Grigorchuk group has superpolynomial growth, at least exp(n^α)
-- statement:
--   The (first) Grigorchuk group $\Gamma = \langle a, b, c, d\rangle$ has superpolynomial growth, and
--   moreover its growth function is at least $\exp(n^\alpha)$ up to constants: for every
--   finite generating set $S$ of $\Gamma$, writing $\gamma(n) = |B_S(n)|$ for the ball of radius $n$,
--
--   $$\frac{\ln \gamma(n)}{\ln n} \to \infty, \qquad \exp(n^\alpha) \le C\,\gamma(Kn) \quad (n \ge 1)$$
--
--   for some $\alpha > 0$, $C > 0$ and integer $K \ge 1$.
--
--   **Formalization Note.** $\Gamma$ is the published `Garrido.GrigorchukGroup` (the same group:
--   Grigorchuk–Pak's $b, c, d$ satisfy $b = (a, c)$, $c = (a, d)$, $d = (1, b)$), and $B_S(n)$ is
--   `Chou.wordBall`. "Superpolynomial" is the paper's definition on p. 2, $\ln\gamma(n)/\ln n \to \infty$.
--   "$\gamma \succcurlyeq \exp(n^\alpha)$" is the paper's $f \preccurlyeq g$ ($f(n) \le C\,g(\beta n)$ for all
--   $n > 0$ and some $C, \beta > 0$) with the scaling $\beta$ taken to be a positive integer $K$, which is
--   equivalent since $\gamma$ is increasing. The paper speaks of *the* growth of $\Gamma$ because the growth
--   class does not depend on the generating set (Exercise 1.3), so both statements are made for every
--   finite generating set.
-- source:
--   R. Grigorchuk and I. Pak, "Groups of intermediate growth: an introduction for beginners", arXiv:math/0607384v1 (2006), p. 10, Corollary 6.5; https://arxiv.org/abs/math/0607384

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace GrigorchukPak

theorem superpolynomial_and_exp_rpow_le_card_wordBall (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          Real.log n) Filter.atTop Filter.atTop ∧
      ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
        Real.exp ((n : ℝ) ^ α) ≤
          C * (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) (K * n)) : ℝ) := by
  sorry

end GrigorchukPak
