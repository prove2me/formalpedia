-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_expect_inter_lower
-- name    : NonmonotoneSubmod.Nonadaptive.expect_inter_lower
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:44:53.527855+00:00
-- url     : https://prove2.me/theorems/39f67a52-d333-4c0a-86f6-5a818a6d72be
-- title:
--   Proof of Theorem 2.6 — $\mathbf{E}[f(R \cap (B \cup C))] \ge \tfrac14 f(C) + \tfrac14 f(B \cup C)$
-- statement:
--   Let $f : 2^X \to \mathbb{R}_{\ge 0}$ be nonnegative and submodular on a finite ground set $X$, let $R = X(1/2)$ be a uniformly random subset of $X$, and let $B, C \subseteq X$ be arbitrary. Then
--
--   $$
--   \mathbf{E}[f(R \cap (B \cup C))] \ge \tfrac14 f(C) + \tfrac14 f(B \cup C).
--   $$
--
--   In the proof of Theorem 2.6, $C$ is an optimal set and the right-hand side is $OPT/4 + \gamma/4$ with $\gamma = f(B \cup C)$; the bound comes from Lemma 2.3 applied to the split $R \cap (B \cup C) = C(1/2) \cup (B \setminus C)(1/2)$.
--
--   **Formalization Note** The expectation is the exact uniform average over the $2^{|X|}$ subsets $S$ of $X$ of $f(S \cap (B \cup C))$. Nonnegativity of $f$ is the paper's standing assumption and is used for the discarded terms $f(\emptyset)$ and $f(B \setminus C)$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1140, §2, proof of Theorem 2.6, third display

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.Nonadaptive

/-- Proof of Theorem 2.6 (Feige–Mirrokni–Vondrák 2011, p. 1140, third display).
For a nonnegative submodular `f`, `R = X(1/2)` and any `B, C ⊆ X`:
`E[f(R ∩ (B ∪ C))] ≥ ¼ f(C) + ¼ f(B ∪ C)`. -/
theorem expect_inter_lower {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (B C : Finset X) :
    (1 / 4) * f C + (1 / 4) * f (B ∪ C) ≤
      NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (B ∪ C))) (fun _ => 1 / 2) := by sorry

end NonmonotoneSubmod.Nonadaptive
