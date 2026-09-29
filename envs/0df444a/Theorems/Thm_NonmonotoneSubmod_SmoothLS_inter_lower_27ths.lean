-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_inter_lower_27ths
-- name    : NonmonotoneSubmod.SmoothLS.inter_lower_27ths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:11:21.24448+00:00
-- url     : https://prove2.me/theorems/2c1cc6c9-d890-4828-b67b-c6848f1c1e88
-- title:
--   §3.2, proof of Theorem 3.6 — lower bound on $\mathbf{E}[f(R \cap (B \cup C))]$ in 27ths
-- statement:
--   Let $f \ge 0$ be submodular on a finite ground set $X$, let $A, C \subseteq X$, $B = X \setminus A$, $R = \mathcal{R}(A, 1/3)$ (elements of $A$ sampled with probability $2/3$, elements of $B$ with probability $1/3$), and $F = (A \cap C) \cup (B \setminus C)$. Then
--
--   $$
--   \mathbf{E}[f(R \cap (B \cup C))] \ge \tfrac{8}{27} f(A \cap C) + \tfrac{2}{27} f(B \cup C) + \tfrac{2}{27} f(B \cap C) + \tfrac{4}{27} f(C) + \tfrac{4}{27} f(F) + \tfrac{1}{27} f(B).
--   $$
--
--   It is the instance of display (∗) for the three disjoint pieces $A\cap C$, $B \cap C$, $B \setminus C$ of $R \cap (B \cup C)$, with the terms $f(\emptyset)$ and $f(B\setminus C)$ dropped by nonnegativity.
--
--   **Formalization Note** $\mathbf{E}[f(R \cap D)]$ is the multilinear extension of $S \mapsto f(S \cap D)$ at the bias-$\tfrac13$ point of $A$; $B$ is written $A^{c}$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1143, §3.2, proof of Theorem 3.6, first display after (∗)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143, first 27ths display (Feige–Mirrokni–Vondrák 2011). Let
`f ≥ 0` be submodular, `A, C ⊆ X`, `B = X \ A`, `R = R(A, 1/3)` and
`F = (A ∩ C) ∪ (B \ C)`. Then
`E[f(R ∩ (B ∪ C))] ≥ (8/27) f(A ∩ C) + (2/27) f(B ∪ C) + (2/27) f(B ∩ C) + (4/27) f(C)
  + (4/27) f(F) + (1/27) f(B)`. -/
theorem inter_lower_27ths {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A C : Finset X) :
    8 / 27 * f (A ∩ C) + 2 / 27 * f (Aᶜ ∪ C) + 2 / 27 * f (Aᶜ ∩ C) + 4 / 27 * f C +
        4 / 27 * f ((A ∩ C) ∪ (Aᶜ \ C)) + 1 / 27 * f Aᶜ ≤
      NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (Aᶜ ∪ C))) (biasPt A (1 / 3)) := by sorry

end NonmonotoneSubmod.SmoothLS
