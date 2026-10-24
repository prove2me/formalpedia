-- Prove2me | Theorems.Thm_IwataFF_SFM_two_cases
-- name    : IwataFF.SFM.two_cases
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:27.312985+00:00
-- url     : https://prove2.me/theorems/7d8bc8af-e0ff-46fe-abf9-06d521e6b2c0
-- title:
--   §4, p. 13 — the two cases: Fix yields a compatible pair $(u, w)$, or an element $w$ with $R(w)$ inside every minimizer
-- statement:
--   Let $n \ge 1$ and $f$ a real submodular function on the subsets of $\{0, \dots, n-1\}$ with $f(\emptyset) = 0$. Consider any state reachable from the initial state of the algorithm of Figure 3 for $f$ that is inside a call of Fix with case flag, element $u$ attaining (4.1), value $\eta$, and current scaling state, and let $w$ be an element Fix may return at that state (end of a phase, $\delta < \kappa/k^3$ with $\kappa = \eta/2$ and $k$ the size of Fix's ground set, $x(w) < -k^2\delta$). Let $f$ also denote the current function and $V$ the current underlying set.
--
--   - In the **former case** ($f(R(u)) \ge \eta/2$, Fix run on $f_u$ over $V \setminus R(u)$): $w \in V \setminus R(u)$ and the pair $(u, w)$ is compatible with $f$.
--   - In the **latter case** (Fix run on $f$ over $V$): every minimizer $X$ of $f$ contains $w$ and contains $R(w)$.
--
--   These two facts make every arc of $D$ compatible and every deleted set part of every minimizer, which is the correctness of Figure 3.
--
--   **Formalization Note** The statement is about states of the algorithm as defined in `IwataFF.SFM.Main` (reachable from the initial state), so the invariants the paper maintains (arcs compatible, cap applied, base consistent) are not assumed but follow from reachability.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 13, §4 (the former and the latter case)

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Definitions.Def_IwataFF_SFM_Main

namespace IwataFF.SFM

open MainState

/-- §4, p. 13 (arXiv:math/0004089v1), the two cases: in every reachable state of Figure 3 where
`Fix` may return `w`, (former case) `w ∈ V \ R(u)` and `(u, w)` is compatible with the current
`f`; (latter case) `w` and all of `R(w)` belong to every minimizer of the current `f`. -/
theorem two_cases {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℝ)
    (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (hs : Relation.ReflTransGen Step (initMain f) s)
    (former : Bool) (u : Finset (Fin n)) (η : ℝ) (ph : PhaseState (Finset (Fin n)))
    (hmode : s.mode = Mode.fix former u η ph) (w : Finset (Fin n))
    (hw : FixOutput (s.fixFun former u) (s.fixGround former u) (η / 2) ph w) :
    (former = true → w ∈ s.blocks \ s.R u ∧ Compatible s.blocks s.curFun u w) ∧
      (former = false → ∀ X, IsMinimizer s.blocks s.curFun X → w ∈ X ∧ s.R w ⊆ X) := by sorry

end IwataFF.SFM
