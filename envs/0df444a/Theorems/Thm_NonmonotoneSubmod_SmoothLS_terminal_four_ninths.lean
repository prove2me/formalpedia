-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_terminal_four_ninths
-- name    : NonmonotoneSubmod.SmoothLS.terminal_four_ninths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:12:32.104783+00:00
-- url     : https://prove2.me/theorems/3c994389-4cd4-4f1c-9e69-3ea22a9e5bd0
-- title:
--   §3.2, proof of Theorem 3.6 — $\mathbf{E}[f(R)] + \frac19 f(B) + \frac2n OPT \ge \frac49 OPT$ at termination
-- statement:
--   Let $f \ge 0$ be submodular on a finite ground set $X$ with $n = |X| \ge 1$ elements and $OPT = \max_{S \subseteq X} f(S)$. Let $A \subseteq X$, $B = X \setminus A$, satisfy the terminal conditions of Algorithm SLS with $\delta = 1/3$:
--
--   $$
--   \omega_{A,1/3}(x) \ge -\tfrac{3}{n^2} OPT \ \ (x \in A), \qquad \omega_{A,1/3}(x) \le \tfrac{3}{n^2} OPT \ \ (x \in B).
--   $$
--
--   Then, with $R = \mathcal{R}(A, 1/3)$,
--
--   $$
--   \mathbf{E}[f(R)] + \tfrac{1}{9} f(B) + \tfrac{2}{n} OPT \ge \tfrac{4}{9} OPT.
--   $$
--
--   This is the concluding inequality of the analysis of Algorithm SLS: at an approximate smoothed local optimum, the random set $R$ and the complement $B$ together capture $4/9$ of the optimum, up to $\frac{2}{n}OPT$.
--
--   **Formalization Note** $\mathbf{E}[f(R)]$ is $\Phi_{1/3}(A)$, the multilinear extension of $f$ at the bias-$\tfrac13$ point of $A$. $n \ge 1$ is assumed (`Nonempty X`).
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1144, §3.2, proof of Theorem 3.6, final chain of displays

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, proof of Theorem 3.6, p. 1144, final chain (Feige–Mirrokni–Vondrák 2011). Let `f ≥ 0`
be submodular on a ground set of `n = |X| ≥ 1` elements, and let `A ⊆ X`, `B = X \ A`, satisfy
the terminal conditions `ω_{A,1/3}(x) ≥ -(3/n²) OPT` for all `x ∈ A` and
`ω_{A,1/3}(x) ≤ (3/n²) OPT` for all `x ∈ B`. Then, with `R = R(A, 1/3)`,
`E[f(R)] + (1/9) f(B) + (2/n) OPT ≥ (4/9) OPT`. -/
theorem terminal_four_ninths {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Finset X)
    (hA : ∀ x, x ∈ A → -(3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ≤ omegaB f A (1 / 3) x)
    (hB : ∀ x, x ∉ A → omegaB f A (1 / 3) x ≤ 3 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) :
    4 / 9 * NonmonotoneSubmod.Shared.OPT f ≤ Phi f (1 / 3) A + 1 / 9 * f Aᶜ + 2 / (Fintype.card X : ℝ) * NonmonotoneSubmod.Shared.OPT f := by sorry

end NonmonotoneSubmod.SmoothLS
