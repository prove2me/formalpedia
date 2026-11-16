-- Prove2me | Theorems.Thm_IntervalExplore_KT1_Supplement_theorem_1
-- name    : IntervalExplore.KT1.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:01:05.932796+00:00
-- url     : https://prove2.me/theorems/2b8d80a7-d55a-4739-a495-938941d4d71a
-- title:
--   Theorem 1 — deterministic KT0 exploration in $O((m-n+1)n+n\log^2 n)$ time
-- statement:
--   There exist a natural-number constant $c\ge1$, a real constant $C>0$ and one deterministic KT0 algorithm $A$ (its decisions depend only on the current identifier, the available ports and the incoming port along the history) with the following property. Let $G=(V,E)$ be any finite simple graph with $n=|V|\ge3$ and $m=|E|\ge n$, with arbitrary distinct identifiers, fixed port numberings and starting vertex, and let the schedule be $\tau_c(n,m)$-interval-connected, where
--   $$
--   \xi(n,m)=\frac{\ln n}{1+\ln m-\ln n},\qquad
--   \tau_c(n,m)=c\left\lceil\xi(n,m)m+n(\ln n)^2\right\rceil .
--   $$
--   Then the agent running $A$ visits every vertex and terminates within
--   $$
--   \Big\lfloor C\big((m-n+1)\,n+n\log_2^2 n\big)\Big\rfloor
--   $$
--   time steps.
--
--   This is the KT0 counterpart of the mission's goal (Theorem 2): the window has the same order, while the exploration time is governed by the cyclomatic number $m-n+1$. Theorem 4 shows the time bound is tight when $m=n+\Omega(\log^2 n)$.
--
--   **Formalization Note** The paper writes $\tau(n,m)=O(\xi m+n\log^2 n)$ for the window; the proof (§2, p.5) uses precisely the witness $\tau_c$ with a sufficiently large universal $c$, as in the published goal. The paper's time $O((m-n+1)n+n\log^2 n)$ becomes the explicit bound with a universal $C$. The constants $c$, $C$ and the algorithm $A$ are chosen before every instance; $A$ does not know $n$, $m$ or the window. The bound $m\le\binom n2$ is automatic for a simple graph.
--
--   Differences from the source:
--   - encoding: τ(n,m)=O(ξ(n,m)m+n log² n) → the §2 witness τ=c·⌈ξ(n,m)m+n(ln n)²⌉ with ∃c≥1 before every instance; reason: this is the function the paper's proof uses (§2, p.5) and it has the printed order; same reading as the published goal
--   - encoding: exploration time O((m−n+1)n+n log² n) → ∃C>0, fixed before every instance, with deadline ⌊C((m−n+1)n+n log₂² n)⌋; reason: n ≥ 3 makes the expression positive, so an absolute constant is the O(·) bound
--   - encoding: a deterministic algorithm in the KT0 model → a published observation-history algorithm whose decisions are invariant under erasing neighbour identifiers; reason: the KT0 input (id, available ports, incoming port) is exactly the published observation without neighbour identifiers; the execution semantics are the published ones
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Theorem 1, p.4 (PDF p.5), with the §2 witness τ, p.5 (PDF p.6); proof §2.2, pp.9–12 (PDF pp.10–13) and Appendix B

import Definitions.Def_IntervalExplore_KT1_Supplement_Model
import Definitions.Def_IntervalExplore_KT1_Rates

set_option autoImplicit false

namespace IntervalExplore.KT1.Supplement

open IntervalExplore.KT1

/-- Theorem 1, p.4 (PDF p.5), with the §2, p.5 (PDF p.6) window witness tau c.
One KT0 algorithm, one window constant c ≥ 1 and one time constant C > 0 are fixed
before every instance; the agent visits every vertex AND terminates within
⌊C·((m−n+1)n + n log₂² n)⌋ steps. -/
theorem theorem_1 :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ C : ℝ, 0 < C ∧ ∃ A : Alg, IsKT0 A ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (W : World V),
        3 ≤ Fintype.card V → Fintype.card V ≤ edgeCount W.graph →
        IntervalConnected W.dynamic (tau c (Fintype.card V) (edgeCount W.graph)) →
        ExploresWithin W A
          ⌊C * (((edgeCount W.graph : ℝ) - Fintype.card V + 1) * Fintype.card V +
              Fintype.card V * (Real.logb 2 (Fintype.card V)) ^ 2)⌋₊ := by sorry

end IntervalExplore.KT1.Supplement
