-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_theorem_7_6_1
-- name    : MDPFinance.InfiniteHorizonApplications.theorem_7_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:05.677873+00:00
-- url     : https://prove2.me/theorems/5918ae7d-0754-4bb9-b735-3a53295dd219
-- title:
--   Theorem 7.6.1 — the infinite-horizon cash balance value function is a convex (s,S)-policy
-- statement:
--   The classical $(s,S)$-inventory-policy result extends to the infinite horizon: the value function
--   has the same three-region shape as its finite-horizon counterpart (chunk `02d`'s Theorem 2.6.2),
--   is convex, and the optimal policy orders up to a fixed critical level $S^-$ (from below) or $S^+$
--   (reordering downward from above), with $S^-$, $S^+$ obtained as accumulation points of the
--   finite-horizon critical-level sequences. Chunk `02d`'s own finite-horizon construction of those
--   sequences is taken as a hypothesis here (cited by name), not re-derived — this mission's own
--   content is the infinite-horizon extension via chunk `07a`'s Theorem 7.1.8, not a second proof of
--   the finite-horizon theory.
--
--   **Moderation note.** The draft's "$J_\infty$" was a free function `Jinfty` unrelated to the model (the theorem claimed an arbitrary function satisfies the recursion, which is refutable), its sequences $(S_n^\pm)$ were arbitrary sequences in an interval, and its optimality clause equated a cost with a negative reward. Now the statement is about the model's $J_\infty$, $J_n$, $J$: finiteness, convexity, $J_\infty=J$, existence of the finite-horizon critical levels with Theorem 2.6.2's three-region form of $J_n$, existence of accumulation points along a common subsequence, and for every such pair $(S^-,S^+)$: $S^-\le S^+$, the three-region formula for $J_\infty$ and optimality of the $(S^-,S^+)$-rule.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 225, Theorem 7.6.1

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_CashBalance

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Theorem 7.6.1 (Bäuerle–Rieder, p. 225, PDF 236). For the cash balance problem with infinite
horizon it holds: a) There exist critical levels `S^-` and `S^+` such that `J_\infty` is given by
the three-region formula (as in Theorem 2.6.2, `J_{n-1}` replaced by `J_\infty`); `J_\infty` is
convex and `J_\infty = J = \lim_n J_n`. b) The stationary policy `(f^*,f^*,\dots)` is optimal with
`f^*(x) := S^-` if `x<S^-`, `x` if `S^-\le x\le S^+`, `S^+` if `x>S^+`, where `S^-`, `S^+` are
accumulation points of the sequences `(S_n^-)`, `(S_n^+)` given in Theorem 2.6.2. Stated with
the model's own value functions (`Jinf`, `Jn`, `Jlim`, costs in `[0,∞]`): the finite-horizon
critical levels `(S_n^±)` of Theorem 2.6.2 are asserted to exist with that theorem's three-region
form of `J_n`; for every pair of accumulation points obtained along a common subsequence (the
accumulation points of the sequence of pairs, which is what the book's proof via policy
iteration produces), `S^- ≤ S^+`, `J_∞` has the three-region form and the `(S^-,S^+)`-rule is
optimal. -/
theorem theorem_7_6_1 (Mk : CashBalanceMarket) :
    (∀ x, Mk.Jinf x < ⊤) ∧
      ConvexOn ℝ Set.univ (fun x => (Mk.Jinf x).toReal) ∧
      (∀ x, Mk.Jinf x = Mk.Jlim x) ∧
      (∃ Sminus Splus : ℕ → ℝ,
        (∀ n, 1 ≤ n → Sminus n ≤ Splus n ∧ ∀ x, Mk.Jn n x =
          if x < Sminus n then
            ENNReal.ofReal ((Sminus n - x) * Mk.cu + Mk.L (Sminus n)) +
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Sminus n - z) ∂Mk.μZ
          else if x ≤ Splus n then
            ENNReal.ofReal (Mk.L x) + ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (x - z) ∂Mk.μZ
          else
            ENNReal.ofReal ((x - Splus n) * Mk.cd + Mk.L (Splus n)) +
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Splus n - z) ∂Mk.μZ) ∧
        (∃ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ ∧
          Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) ∧
          Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp)) ∧
        ∀ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ →
          Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) →
          Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp) →
          Sm ≤ Sp ∧
          (∀ x, Mk.Jinf x =
            if x < Sm then
              ENNReal.ofReal ((Sm - x) * Mk.cu + Mk.L Sm) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jinf (Sm - z) ∂Mk.μZ
            else if x ≤ Sp then
              ENNReal.ofReal (Mk.L x) + ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jinf (x - z) ∂Mk.μZ
            else
              ENNReal.ofReal ((x - Sp) * Mk.cd + Mk.L Sp) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jinf (Sp - z) ∂Mk.μZ) ∧
          ∀ x, Mk.Jinfpi (fun _ => cbRule Sm Sp) x = Mk.Jinf x) := by sorry

end MDPFinance.InfiniteHorizonApplications
