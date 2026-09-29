-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_terminal_upper_estimates
-- name    : NonmonotoneSubmod.SmoothLS.terminal_upper_estimates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:10:44.766868+00:00
-- url     : https://prove2.me/theorems/dd75aed6-7588-4daa-9618-d988d5208b6a
-- title:
--   §3.2, proof of Theorem 3.6 — at termination, $\mathbf{E}[f(R \cup (B\cap C))], \mathbf{E}[f(R \cap (B\cup C))] \le \mathbf{E}[f(R)] + \frac{2}{n}OPT$
-- statement:
--   Let $f \ge 0$ be submodular on a finite ground set $X$ with $n = |X| \ge 1$ elements and $OPT = \max_{S\subseteq X} f(S)$. Let $A \subseteq X$, $B = X \setminus A$, and let $R = \mathcal{R}(A, 1/3)$, so that elements of $A$ are sampled with probability $p = 2/3$ and elements of $B$ with probability $q = 1/3$. For every $C \subseteq X$:
--
--   1. if $\omega_{A,1/3}(x) \le \frac{3}{n^2} OPT$ for every $x \in B$, then
--   $$
--   \mathbf{E}[f(R \cup (B \cap C))] \le \mathbf{E}[f(R)] + \frac{2}{n} OPT;
--   $$
--   2. if $\omega_{A,1/3}(x) \ge -\frac{3}{n^2} OPT$ for every $x \in A$, then
--   $$
--   \mathbf{E}[f(R \cap (B \cup C))] \le \mathbf{E}[f(R)] + \frac{2}{n} OPT.
--   $$
--
--   The two hypotheses are exactly what the termination of Algorithm SLS guarantees for the true smoothed marginals; the conclusions let the analysis replace the returned random set $R$ by $R \cup (B\cap C)$ and $R \cap (B \cup C)$ at a cost of $\frac{2}{n}OPT$.
--
--   **Formalization Note** $\mathbf{E}[f(R \cup D)]$ and $\mathbf{E}[f(R \cap D)]$ are the multilinear extensions of $S \mapsto f(S\cup D)$ and $S \mapsto f(S \cap D)$ at the bias-$\tfrac13$ point of $A$. $n \ge 1$ is assumed (`Nonempty X`) so that $\frac{2}{n}$ and $\frac{3}{n^2}$ are not the Lean junk value of division by $0$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1143, §3.2, proof of Theorem 3.6, second paragraph and display, and the sentence 'Similarly, we can obtain ...' (pp. 1143)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1143, second paragraph and display (Feige–Mirrokni–Vondrák
2011). Let `f ≥ 0` be submodular on a ground set of `n = |X| ≥ 1` elements, `A ⊆ X`, `B = X \ A`,
and `R = R(A, 1/3)`. For every `C ⊆ X`:
* if `ω_{A,1/3}(x) ≤ (3/n²) OPT` for all `x ∈ B`, then `E[f(R ∪ (B ∩ C))] ≤ E[f(R)] + (2/n) OPT`;
* if `ω_{A,1/3}(x) ≥ -(3/n²) OPT` for all `x ∈ A`, then `E[f(R ∩ (B ∪ C))] ≤ E[f(R)] + (2/n) OPT`. -/
theorem terminal_upper_estimates {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Finset X) :
    ((∀ x, x ∉ A → omegaB f A (1 / 3) x ≤ 3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) →
      ∀ C : Finset X, NonmonotoneSubmod.Shared.F (fun S => f (S ∪ (Aᶜ ∩ C))) (biasPt A (1 / 3)) ≤
        Phi f (1 / 3) A + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f) ∧
    ((∀ x, x ∈ A → -(3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ≤ omegaB f A (1 / 3) x) →
      ∀ C : Finset X, NonmonotoneSubmod.Shared.F (fun S => f (S ∩ (Aᶜ ∪ C))) (biasPt A (1 / 3)) ≤
        Phi f (1 / 3) A + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f) := by sorry

end NonmonotoneSubmod.SmoothLS
