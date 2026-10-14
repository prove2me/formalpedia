-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_gChar_characterization
-- name    : NetFeePlatform.Competition.gChar_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:47.803125+00:00
-- url     : https://prove2.me/theorems/01af9e1e-f7a1-4c41-b582-001608842c58
-- title:
--   Proof of Proposition 4, p. 49 — the zeros of g(n; J) are exactly the equilibria with one dominant and J − 1 equal small platforms
-- statement:
--   Consider the one-sided Logit platform game with no outside option, $J\ge2$ platforms, common marginal cost $c$, common interaction value $\gamma$ and no interoperability. Let $0<n<1$, fix a platform $i$, and let $g(n;J)$ be the characterization function
--   $$g(n;J)=\ln n-\ln(J-1)-\ln(1-n)+\frac{1}{1-\frac{n}{J-1}}-2\gamma\frac{n}{J-1}-\Big(\frac1n-2\gamma(1-n)\Big).$$
--
--   1. If $t$ is an equilibrium in which platform $i$ has share $1-n$ and every other platform has share $n/(J-1)$, then $g(n;J)=0$.
--   2. If $\gamma\le 27/8$ and $g(n;J)=0$, then there is an equilibrium $t$ in which platform $i$ has share $1-n$ and every other platform has share $n/(J-1)$.
--
--   This makes precise the paper's description of $g(n;J)$ as "a characterization function whose zeros are equilibria": existence and comparison of equilibria with one dominant platform reduce to locating the zeros of a real function of one variable.
--
--   **Formalization Note** "No outside option" is the weight $w=e^{z}=0$. Equilibrium is the global Nash condition over all deviations. The converse direction needs $\gamma\le27/8$, the range in which the pricing formula is sufficient for a best response; Proposition 4 assumes this range.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 49, Appendix E.2, proof of Proposition 4

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_Competition_GChar

namespace NetFeePlatform.Competition
theorem gChar_characterization (c γ : ℝ) (J : ℕ) (hJ : 2 ≤ J) (n : ℝ)
    (hn0 : 0 < n) (hn1 : n < 1) (i : Fin J) :
    (∀ t : Fin J → ℝ, IsEquilibrium 0 c γ 0 t → demand 0 t i = 1 - n →
        (∀ k, k ≠ i → demand 0 t k = n / ((J : ℝ) - 1)) → gChar γ J n = 0) ∧
    (γ ≤ 27 / 8 → gChar γ J n = 0 →
      ∃ t : Fin J → ℝ, IsEquilibrium 0 c γ 0 t ∧ demand 0 t i = 1 - n ∧
        ∀ k, k ≠ i → demand 0 t k = n / ((J : ℝ) - 1)) := by sorry
end NetFeePlatform.Competition
