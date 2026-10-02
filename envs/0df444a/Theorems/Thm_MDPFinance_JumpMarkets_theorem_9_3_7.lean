-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_theorem_9_3_7
-- name    : MDPFinance.JumpMarkets.theorem_9_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:42.314264+00:00
-- url     : https://prove2.me/theorems/6736090f-5872-4e22-85b2-145f6452a24c
-- title:
--   Theorem 9.3.7 — stability of the value and of the optimal policies under utility perturbation
-- statement:
--   **Theorem 9.3.7** (p. 290).
--
--   a) If $U$ and $\tilde U$ are two utility functions with corresponding value functions $V$ and
--      $\tilde V$, then $\|V - \tilde V\|_b \le \|U - \tilde U\|_b\,e^{T\barμ}/(1-\alpha_b)$.
--   b) Let $(U^{(n)})$ be a sequence of utility functions with
--      $\lim_{n\to\infty}\|U^{(n)} - U\|_b = 0$. Then it holds
--      $\emptyset \ne \mathrm{Ls}\,A^*_n(t,x) \subset A^*(t,x)$ for all $(t,x) \in E$, i.e. in
--      particular, the limit $f^*$ of a sequence $(f^*_n)$ with $f^*_n(t,x) \in A^*_n(t,x)$ for all
--      $(t,x) \in E$ defines an optimal stationary policy for the given model (with utility function
--      $U$).
--
--   The practical payoff of the contracting structure: a utility function is never known exactly, and
--   this says the answer degrades gracefully. a) is a Lipschitz estimate for the value with the
--   explicit constant $e^{T\barμ}/(1-\alpha_b)$; b) is the corresponding statement for the *optimal
--   policies*, which is strictly stronger and does not follow from a) — value functions can be close
--   while argmax sets are far apart.
--
--   **b) is an upper-limit statement, not a limit.** $\mathrm{Ls}\,A^*_n(t,x)$ is the book's own
--   definition (p. 201): an accumulation point of *some* sequence $(a_n)$ with
--   $a_n \in A^*_n(t,x)$ — a statement about a sequence of points, not a `Filter.limsup` of sets, and
--   rendered here as chunk `07a` renders it. Both halves are the content: $\emptyset \ne \mathrm{Ls}$
--   says approximating policies *have* accumulation points, and the inclusion says every such point is
--   optimal for the true utility.
--
--   a) is stated in its $\le$-form against the bounding function rather than by forming
--   $\|\cdot\|_b$, which is itself a supremum.
--
--   **Moderation note.** In the draft the approximating markets `M_n` were arbitrary (not the same market with a different utility — refutable), their `V_n` arbitrary fixed points, and `Ls` was in an arbitrary topology. Now `M_n` share the market data, `V`, `Ṽ`, `V^{(n)}` are the value functions, a) is a two-sided `[0,∞]` bound with the constant `e^{T\barμ}/(1 − α_b)`, and b) is `∅ ≠ Ls A^*_n(t,x) ⊂ A^*(t,x)` over the relaxed controls with the Young topology.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 290 (PDF 300), Theorem 9.3.7

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- Two jump markets with the same market data, differing only in the utility. -/
def JumpMarket.SameMarket {d : ℕ} (M M' : JumpMarket d) : Prop :=
  M'.rho = M.rho ∧ M'.mu = M.mu ∧ M'.lam = M.lam ∧ M'.QY = M.QY ∧ M'.T = M.T

/-- **Theorem 9.3.7** (p. 290), for the contracting model (`b = b_γ`, `α_b < 1`). a) If `U`,
`Ũ` are two utility functions (same market) with value functions `V`, `Ṽ`, then `‖V - Ṽ‖_b ≤
‖U - Ũ‖_b e^{T\barμ}/(1-α_b)` (in `≤`-form against `b`, two-sided in `[0,∞]`). b) If `(U^{(n)})`
are utility functions with `‖U^{(n)} - U‖_b → 0` and `V^{(n)}` their value functions, then
`∅ ≠ Ls A^*_n(t,x) ⊂ A^*(t,x)` on `E`, the maximum-point sets over the relaxed controls `R`
with the Young topology. -/
theorem theorem_9_3_7 {d : ℕ} (M Mtilde : JumpMarket d)
    (gamma alpha : ℝ) (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (hbt : Mtilde.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1)
    (hsame : M.SameMarket Mtilde)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    (∀ C : ℝ, (∀ p ∈ M.E, |M.U p.2 - Mtilde.U p.2| ≤ C * M.bfun gamma p) →
      ∀ p ∈ M.E,
        M.V Pr p ≤ Mtilde.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p) ∧
          Mtilde.V Pr p ≤ M.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p)) ∧
    (∀ Mn : ℕ → JumpMarket d, (∀ n, M.SameMarket (Mn n)) →
      (∀ n, (Mn n).IsBoundingFunction (M.bfun gamma) alpha) →
      (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ p ∈ M.E,
        |(Mn n).U p.2 - M.U p.2| ≤ ε * M.bfun gamma p) →
      ∀ p ∈ M.E,
        (LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p)).Nonempty ∧
        LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p) ⊆ M.AstarRel (M.V Pr) p) := by sorry

end MDPFinance.JumpMarkets
