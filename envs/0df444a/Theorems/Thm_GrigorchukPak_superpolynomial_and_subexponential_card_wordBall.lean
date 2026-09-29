-- Prove2me | Theorems.Thm_GrigorchukPak_superpolynomial_and_subexponential_card_wordBall
-- name    : GrigorchukPak.superpolynomial_and_subexponential_card_wordBall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T14:24:34.51441+00:00
-- url     : https://prove2.me/theorems/cbafe773-c322-4cf1-ada3-ae0023b60f2a
-- title:
--   Grigorchuk–Pak, Theorem 4.1 — the Grigorchuk group has intermediate growth
-- statement:
--   The (first) Grigorchuk group $\Gamma = \langle a, b, c, d\rangle$ has intermediate growth: its
--   growth function is both superpolynomial and subexponential. For every finite generating set $S$,
--   writing $\gamma(n) = |B_S(n)|$,
--
--   $$\frac{\ln \gamma(n)}{\ln n} \to \infty \qquad\text{and}\qquad \frac{\ln \gamma(n)}{n} \to 0.$$
--
--   **Formalization Note.** Both limits are the paper's definitions on p. 2 (superpolynomial;
--   subexponential), and "intermediate growth" is their conjunction (p. 3). $\Gamma$ is the published
--   `Garrido.GrigorchukGroup` and $B_S(n)$ is `Chou.wordBall`. The statement is made for every finite
--   generating set, as the paper's "group $\Gamma$ has intermediate growth" is (Exercise 1.3).
-- source:
--   R. Grigorchuk and I. Pak, "Groups of intermediate growth: an introduction for beginners", arXiv:math/0607384v1 (2006), p. 7, Theorem 4.1 (Main Theorem); https://arxiv.org/abs/math/0607384

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace GrigorchukPak

theorem superpolynomial_and_subexponential_card_wordBall (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          Real.log n) Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun n : ℕ => Real.log (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) /
          n) Filter.atTop (nhds 0) := by
  sorry

end GrigorchukPak
