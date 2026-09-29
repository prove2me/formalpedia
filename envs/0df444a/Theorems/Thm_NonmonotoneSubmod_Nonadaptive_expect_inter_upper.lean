-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_expect_inter_upper
-- name    : NonmonotoneSubmod.Nonadaptive.expect_inter_upper
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:42:51.599136+00:00
-- url     : https://prove2.me/theorems/24ac759d-6538-479a-a4ed-0f61a52d08be
-- title:
--   Proof of Theorem 2.6 — $\mathbf{E}[f(R)] \ge \mathbf{E}[f(R \cap (B \cup C))] - OPT/(2n)$
-- statement:
--   Let $X$ be a nonempty finite ground set with $n = |X|$ elements, let $f : 2^X \to \mathbb{R}_{\ge 0}$ be nonnegative and submodular with optimum $OPT$, let $R = X(1/2)$ be a uniformly random subset of $X$, and let $\omega$ be as in Definition 2.4. Let $A \subseteq X$ be a set with
--
--   $$
--   \omega(x) \ge -\frac{OPT}{n^2} \quad \text{for every } x \in A,
--   $$
--
--   and let $B = X \setminus A$. Then for every $C \subseteq X$,
--
--   $$
--   \mathbf{E}[f(R)] \ge \mathbf{E}[f(R \cap (B \cup C))] - \frac{OPT}{2n}.
--   $$
--
--   Removing from the random set the elements of $A \setminus C$, whose averaged marginal values are at least $-OPT/n^2$, can increase the expected value by at most $OPT/(2n)$. It is the mirror image of the upper estimate for $\mathbf{E}[f(R \cup (B \cap C))]$.
--
--   **Formalization Note** $B$ is the complement `Aᶜ` of $A$; both expectations are exact uniform averages over the $2^n$ subsets of $X$. The ground set is assumed nonempty so that the divisions by $n$ are genuine. Nonnegativity of $f$ gives $OPT \ge 0$, used in the step $-|A \setminus C|\,OPT/(2n^2) \ge -OPT/(2n)$. The page writes "$=$" before $-|A\setminus C|\,OPT/(2n^2)$; since each summand is only bounded below by $-OPT/(2n^2)$, the correct relation is "$\ge$", and the statement here is the inequality the argument proves.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1140, §2, proof of Theorem 2.6, first and second displays

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Nonadaptive_omega

namespace NonmonotoneSubmod.Nonadaptive

/-- Proof of Theorem 2.6 (Feige–Mirrokni–Vondrák 2011, p. 1140, first two displays).
Let `f` be nonnegative and submodular on a nonempty ground set of `n` elements, `R = X(1/2)`.
If `ω(x) ≥ −OPT/n²` for every `x ∈ A`, and `B = X \ A`, then for every `C ⊆ X`,
`E[f(R)] ≥ E[f(R ∩ (B ∪ C))] − OPT/(2n)`. -/
theorem expect_inter_upper {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A C : Finset X)
    (hA : ∀ x ∈ A, -(NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2) ≤ omega f x) :
    NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (Aᶜ ∪ C))) (fun _ => 1 / 2) - NonmonotoneSubmod.Shared.OPT f / (2 * (Fintype.card X : ℝ)) ≤
      NonmonotoneSubmod.Shared.F f (fun _ => 1 / 2) := by sorry

end NonmonotoneSubmod.Nonadaptive
