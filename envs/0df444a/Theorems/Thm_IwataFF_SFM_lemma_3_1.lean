-- Prove2me | Theorems.Thm_IwataFF_SFM_lemma_3_1
-- name    : IwataFF.SFM.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:26.914276+00:00
-- url     : https://prove2.me/theorems/c032c715-ac4f-4ac5-9c40-3134c55f378f
-- title:
--   Lemma 3.1 — if $Z = \emptyset$, then $W$ is tight for $x$
-- statement:
--   Let $V$ be a finite nonempty set and $f$ submodular on $V$ with $f(\emptyset) = 0$. Consider a state of the scaling algorithm satisfying the invariants (every $L_i$ a linear ordering of $V$, $\lambda_i > 0$, $\sum_i \lambda_i = 1$, $\varphi$ skew-symmetric and $\delta$-feasible, $\delta > 0$), with $x = \sum_i \lambda_i y_i$ and $W$ the set of vertices reachable from $S$ in the residual graph. If there is no active pair ($Z = \emptyset$), then $W$ is tight for $x$:
--   $$x(W) = f(W).$$
--
--   **Formalization Note** States are those of the definition `IwataFF.SFM.Phase`; the real-valued $f$ replaces §3's integer-valued one (the proof never uses integrality).
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 10, Lemma 3.1

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase

namespace IwataFF.SFM

/-- Lemma 3.1 (arXiv:math/0004089v1, p. 10): if `Z = ∅`, then `W` is tight for `x`. -/
theorem lemma_3_1 {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (hZ : ¬ ZNonempty f V st) :
    xsum (xOf f st) (Wset f V st) = f (Wset f V st) := by sorry

end IwataFF.SFM
