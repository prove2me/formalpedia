-- Prove2me | Theorems.Thm_IwataFF_SFM_lemma_3_3
-- name    : IwataFF.SFM.lemma_3_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:26.901189+00:00
-- url     : https://prove2.me/theorems/697c00a4-f5cd-449d-ac97-7ddada8422f4
-- title:
--   Lemma 3.3 — relaxed strong duality at the end of each δ-scaling phase, cases (i)–(iii)
-- statement:
--   Let $V$ be a finite nonempty set with $|V| = n$ and $f$ submodular on $V$ with $f(\emptyset) = 0$. Consider a state of the scaling algorithm satisfying the invariants and at the **end of a $\delta$-scaling phase**: $S = \emptyset$, or $T = \emptyset$, or ($Z = \emptyset$ and $W \cap T = \emptyset$). Let $x = \sum_i \lambda_i y_i$ and $z = x - \partial\varphi$. Then:
--
--   (i) if $S = \emptyset$, then $x^-(V) \ge f(\emptyset) - n^2\delta$ and $z^-(V) \ge f(\emptyset) - n\delta$;
--
--   (ii) if $T = \emptyset$, then $x^-(V) \ge f(V) - n^2\delta$ and $z^-(V) \ge f(V) - n\delta$;
--
--   (iii) if $W$ is tight for $x$ ($x(W) = f(W)$), then
--   $$x^-(V) \ge f(W) - n^2\delta \quad\text{and}\quad z^-(V) \ge f(W) - n\delta.$$
--
--   **Formalization Note** "End of a phase" is the end condition of the paper's prose (p. 10: "In the last case, we have … $W \cap T = \emptyset$"), not Figure 1's printed guard, under which (iii) fails. It is stated for every state with the invariants, not only for reachable ones, since the proof uses nothing else. $f$ is real-valued (§3 assumes integers; the proof never uses them, and §4 applies the lemma to real $f$).
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 10, Lemma 3.3

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase

namespace IwataFF.SFM

/-- Lemma 3.3 (arXiv:math/0004089v1, p. 10): at the end of a δ-scaling phase, (i)–(iii) hold
for `x` and `z = x − ∂ϕ` (`n = |V|`). -/
theorem lemma_3_3 {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (hend : PhaseEnd f V st) :
    (Sset f V st = ∅ →
        f ∅ - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V ∧
        f ∅ - (V.card : ℝ) * st.delta ≤ xsum (xneg (zOf f V st)) V) ∧
      (Tset f V st = ∅ →
        f V - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V ∧
        f V - (V.card : ℝ) * st.delta ≤ xsum (xneg (zOf f V st)) V) ∧
      (xsum (xOf f st) (Wset f V st) = f (Wset f V st) →
        f (Wset f V st) - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V ∧
        f (Wset f V st) - (V.card : ℝ) * st.delta ≤ xsum (xneg (zOf f V st)) V) := by sorry

end IwataFF.SFM
