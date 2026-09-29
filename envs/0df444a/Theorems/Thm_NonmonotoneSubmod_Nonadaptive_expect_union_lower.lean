-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_expect_union_lower
-- name    : NonmonotoneSubmod.Nonadaptive.expect_union_lower
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:37:10.820001+00:00
-- url     : https://prove2.me/theorems/3e423bc6-5fba-4fb0-92e9-de5bc42b4cb4
-- title:
--   Proof of Theorem 2.6 — $\mathbf{E}[f(R \cup (B \cap C))] \ge \tfrac14 f(B\cap C) + \tfrac14 f(C)$
-- statement:
--   Let $f : 2^X \to \mathbb{R}_{\ge 0}$ be nonnegative and submodular on a finite ground set $X$, let $R = X(1/2)$ be a uniformly random subset of $X$, and let $B, C \subseteq X$ be arbitrary. Then
--
--   $$
--   \mathbf{E}[f(R \cup (B \cap C))] \ge \tfrac14 f(B \cap C) + \tfrac14 f(C).
--   $$
--
--   In the proof of Theorem 2.6, $C$ is an optimal set and the right-hand side is $\beta/4 + OPT/4$ with $\beta = f(B\cap C)$; the bound comes from applying Lemma 2.3 to the submodular function $g(R) = f(R \cup (B \cap C))$ with the split $R = C(1/2) \cup \bar C(1/2)$.
--
--   **Formalization Note** The expectation is the exact uniform average over the $2^{|X|}$ subsets $S$ of $X$ of $f(S \cup (B \cap C))$. Nonnegativity of $f$ is the paper's standing assumption and is used for the discarded terms $g(\bar C)$ and $g(X)$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1139, §2, proof of Theorem 2.6, last display

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.Nonadaptive

/-- Proof of Theorem 2.6 (Feige–Mirrokni–Vondrák 2011, p. 1139, last display).
For a nonnegative submodular `f`, `R = X(1/2)` and any `B, C ⊆ X`:
`E[f(R ∪ (B ∩ C))] ≥ ¼ f(B ∩ C) + ¼ f(C)`. -/
theorem expect_union_lower {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (B C : Finset X) :
    (1 / 4) * f (B ∩ C) + (1 / 4) * f C ≤
      NonmonotoneSubmod.Shared.F (fun S => f (S ∪ (B ∩ C))) (fun _ => 1 / 2) := by sorry

end NonmonotoneSubmod.Nonadaptive
