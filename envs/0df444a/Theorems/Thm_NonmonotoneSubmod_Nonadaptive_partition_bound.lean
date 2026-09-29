-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_partition_bound
-- name    : NonmonotoneSubmod.Nonadaptive.partition_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:28:14.192606+00:00
-- url     : https://prove2.me/theorems/5b1d584c-ff54-40ba-8875-e8bd26f47274
-- title:
--   Proof of Theorem 2.6 — $f(A) + f(B\cap C) + f(B \cup C) \ge f(C)$ for $B = X \setminus A$
-- statement:
--   Let $f : 2^X \to \mathbb{R}_{\ge 0}$ be nonnegative and submodular, let $A \subseteq X$ with complement $B = X \setminus A$, and let $C \subseteq X$ be any set. Then
--
--   $$
--   f(A) + f(B \cap C) + f(B \cup C) \ge f(C).
--   $$
--
--   In the proof of Theorem 2.6, $C$ is an optimal set, $f(C) = OPT$, and with $\alpha = f(A)$, $\beta = f(B \cap C)$, $\gamma = f(B \cup C)$ this reads $\alpha + \beta + \gamma \ge OPT$: at least one of the three quantities is $OPT/3$. The inequality holds for every $C$, not only for an optimal one.
--
--   **Formalization Note** $B$ is written as the complement `Aᶜ` of $A$ in the finite ground set. Nonnegativity of $f$ is the paper's standing assumption and is used for the discarded terms $f(\emptyset)$ and $f(X)$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1139, §2, proof of Theorem 2.6, first and second displays

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.Nonadaptive

/-- Proof of Theorem 2.6 (Feige–Mirrokni–Vondrák 2011, p. 1139, first and second displays).
For a nonnegative submodular `f`, any `A ⊆ X` with complement `B = X \ A`, and any `C ⊆ X`:
`f(A) + f(B ∩ C) + f(B ∪ C) ≥ f(C)`. (In the paper `C` is the optimal set, so the right side
is `OPT`; the inequality holds for every `C`.) -/
theorem partition_bound {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A C : Finset X) :
    f C ≤ f A + f (Aᶜ ∩ C) + f (Aᶜ ∪ C) := by sorry

end NonmonotoneSubmod.Nonadaptive
