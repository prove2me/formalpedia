-- Prove2me | Theorems.Thm_NonmonotoneSubmod_LocalSearch_ls_approximation
-- name    : NonmonotoneSubmod.LocalSearch.ls_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:06:43.42491+00:00
-- url     : https://prove2.me/theorems/59a5a8ef-1a50-481c-818e-96f6b5060984
-- title:
--   Theorem 3.4 — Algorithm LS is a $(\frac13-\frac{\epsilon}{n})$-approximation, $(\frac12-\frac{\epsilon}{n})$ for symmetric $f$, with $(1+\epsilon/n^2)^k \le n$ steps
-- statement:
--   Let $f : 2^X \to \mathbb{R}_{\ge 0}$ be a nonnegative submodular function on a nonempty finite ground set $X$ with $n = |X|$ elements, let $\mathrm{OPT} = \max_{S \subseteq X} f(S)$, and let $\epsilon > 0$. Run Algorithm LS with acceptance factor $1 + \epsilon/n^2$: start at a singleton $\{v\}$ of maximum value, repeatedly add an element $a$ with $f(S \cup \{a\}) > (1+\epsilon/n^2) f(S)$, and only when no such addition exists remove an element $a$ with $f(S \setminus \{a\}) > (1+\epsilon/n^2) f(S)$. Then:
--
--   1. **Approximation.** Whenever the algorithm terminates at a set $S$ (no step applies), whatever choices it made along the way, the returned value satisfies
--   $$\max\{f(S),\, f(X \setminus S)\} \ge \Big(\frac13 - \frac{\epsilon}{n}\Big)\mathrm{OPT}.$$
--   2. **Symmetric functions.** If moreover $f(X \setminus T) = f(T)$ for all $T$, then at termination
--   $$f(S) \ge \Big(\frac12 - \frac{\epsilon}{n}\Big)\mathrm{OPT}.$$
--   3. **Number of iterations.** If $n \ge 2$, every run of $k$ steps of the algorithm satisfies
--   $$\Big(1 + \frac{\epsilon}{n^2}\Big)^k \le n,$$
--   so $k = O(\tfrac{1}{\epsilon} n^2 \log n)$ and the algorithm terminates.
--
--   This is the deterministic $1/3$-approximation for unconstrained maximization of nonnegative submodular functions, and $1/2$ for symmetric ones, from the value-oracle model.
--
--   **Formalization Note** The printed theorem ends "The algorithm uses at most $O(\frac1\epsilon n^3 \log n)$ oracle calls"; this $O(\cdot)$ has an unquantified constant, so part 3 states instead the explicit step bound that the proof establishes (each step makes at most $2n$ oracle queries). Part 3 needs $n \ge 2$: for $n = 1$, $f(\emptyset) = 5$, $f(\{v\}) = 0$ lets LS take one step, and $(1+\epsilon) \le 1$ fails. Nonnegativity of $f$ is the standing assumption of §3; $\epsilon > 0$ is implicit in the paper; $X \neq \emptyset$ makes the start singleton exist. For symmetric $f$ the returned value $\max\{f(S), f(X\setminus S)\}$ equals $f(S)$. The runs are quantified over every choice of maximizing singleton and of improving element.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, Theorem 3.4 and its proof

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

/-- Theorem 3.4 (Feige–Mirrokni–Vondrák 2011, p. 1141), in the explicit form of its proof.
Let `f ≥ 0` be submodular on a nonempty finite ground set `X` with `n = |X|`, and `ε > 0`.
(a) every terminated run of Algorithm LS returns `max(f(S), f(X \ S)) ≥ (1/3 − ε/n) OPT`;
(b) if `f` is symmetric, every terminated run ends at `S` with `f(S) ≥ (1/2 − ε/n) OPT`;
(c) if `n ≥ 2`, every run of `k` LS steps has `(1 + ε/n²)^k ≤ n`. -/
theorem ls_approximation {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k → IsLSTerminal ε f (S k) →
        (1 / 3 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ lsOutput f (S k)) ∧
    (NonmonotoneSubmod.Shared.SymmetricSetFun f → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        IsLSTerminal ε f (S k) →
        (1 / 2 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ f (S k)) ∧
    (2 ≤ Fintype.card X → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        (1 + ε / (Fintype.card X : ℝ) ^ 2) ^ k ≤ (Fintype.card X : ℝ)) := by sorry

end NonmonotoneSubmod.LocalSearch
