-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_expect_union_upper
-- name    : NonmonotoneSubmod.Nonadaptive.expect_union_upper
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:33:16.176001+00:00
-- url     : https://prove2.me/theorems/771a83fd-b870-496c-b2ef-a75d559b4e2b
-- title:
--   Proof of Theorem 2.6 — $\mathbf{E}[f(R \cup (B \cap C))] \le \mathbf{E}[f(R)] + OPT/(2n)$
-- statement:
--   Let $X$ be a nonempty finite ground set with $n = |X|$ elements, let $f : 2^X \to \mathbb{R}_{\ge 0}$ be nonnegative and submodular with optimum $OPT = \max_{S\subseteq X} f(S)$, let $R = X(1/2)$ be a uniformly random subset of $X$, and let $\omega$ be as in Definition 2.4. Let $B \subseteq X$ be a set with
--
--   $$
--   \omega(x) \le \frac{OPT}{n^2} \quad \text{for every } x \in B .
--   $$
--
--   Then for every $C \subseteq X$,
--
--   $$
--   \mathbf{E}[f(R \cup (B \cap C))] \le \mathbf{E}[f(R)] + \frac{OPT}{2n}.
--   $$
--
--   Adding to the random set the elements of $B$, whose averaged marginal values are at most $OPT/n^2$, can increase the expected value by at most $OPT/(2n)$. In the proof of Theorem 2.6 this lets the analysis replace $\mathbf{E}[f(R)]$ by $\mathbf{E}[f(R \cup (B \cap C))]$ at a cost of $OPT/(2n)$.
--
--   **Formalization Note** Both expectations are exact uniform averages over the $2^n$ subsets of $X$. The ground set is assumed nonempty so that $n \ge 1$ and $OPT/n^2$, $OPT/(2n)$ are not the Lean junk value of division by zero. Nonnegativity of $f$ (the paper's standing assumption) gives $OPT \ge 0$, used in the last step $|B \cap C| \cdot OPT/(2n^2) \le OPT/(2n)$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1139, §2, proof of Theorem 2.6, third and fourth displays (and the sentence before them)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Nonadaptive_omega

namespace NonmonotoneSubmod.Nonadaptive

/-- Proof of Theorem 2.6 (Feige–Mirrokni–Vondrák 2011, p. 1139, third and fourth displays).
Let `f` be nonnegative and submodular on a nonempty ground set of `n` elements, `R = X(1/2)`.
If `ω(x) ≤ OPT/n²` for every `x ∈ B`, then for every `C ⊆ X`,
`E[f(R ∪ (B ∩ C))] ≤ E[f(R)] + OPT/(2n)`. -/
theorem expect_union_upper {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (B C : Finset X)
    (hB : ∀ x ∈ B, omega f x ≤ NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2) :
    NonmonotoneSubmod.Shared.F (fun S => f (S ∪ (B ∩ C))) (fun _ => 1 / 2) ≤
      NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) + NonmonotoneSubmod.Shared.OPT f / (2 * (Fintype.card X : ℝ)) := by sorry

end NonmonotoneSubmod.Nonadaptive
