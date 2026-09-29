-- Prove2me | Theorems.Thm_MultiplicativeFunctions_collapse_iff_completelyMult
-- name    : MultiplicativeFunctions.collapse_iff_completelyMult
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T16:13:32.175533+00:00
-- url     : https://prove2.me/theorems/f9002e3c-3757-4b8b-9dcb-f9ae1547d5c8
-- title:
--   A shift relation characterising complete multiplicativity of $\pm1$ functions
-- statement:
--   **A two-point shift relation is equivalent to complete multiplicativity.**
--
--   Let $f : \mathbb{N} \to \mathbb{R}$ take only the values $\pm1$ on $n \ge 1$, normalised by
--   $f(1) = 1$. Then the following are equivalent:
--
--   1. **the collapse relation** — for every prime $p$ and every $N \ge 1$,
--      $$f(pN)\,f(pN + p) \;=\; f(N)\,f(N+1);$$
--   2. **complete multiplicativity** — $f(ab) = f(a)f(b)$ for all $a, b \ge 1$.
--
--   The first condition says that the two-point correlation $f(n)f(n+1)$ is invariant under
--   dilating $n$ by a prime, which on its face is far weaker than multiplicativity: it constrains
--   only consecutive pairs, and only along dilations. The theorem says that for $\pm1$-valued
--   functions the two are in fact the same condition.
--
--   Functions of this kind are exactly the real characters-like objects appearing in Chowla's
--   conjecture and the Erd\H{o}s discrepancy circle of problems, where the two-point correlation
--   $\sum_{n\le x} f(n)f(n+1)$ is the central object. The equivalence explains why the "collapse"
--   hypothesis, which arises naturally when manipulating such correlations, is not a genuine
--   weakening: any $\pm1$ function satisfying it is a completely multiplicative function, hence
--   essentially a real character.
--
--   **Formalization note.** The hypotheses `hpm` and `h1` fix $f$ to be $\pm1$-valued on $n \ge 1$
--   and normalised; no multiplicativity is assumed on either side of the equivalence.
-- source:
--   Arising in the Chowla / Erdős-discrepancy circle; cf. Tao, *The Erdős discrepancy problem* (2016), and Elliott, *Probabilistic Number Theory*. Lean proof extracted from `Salt/Entropy/Chowla/BoundaryMap.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MultiplicativeFunctions

theorem collapse_iff_completelyMult (f : ℕ → ℝ)
    (hpm : ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1) (h1 : f 1 = 1) :
    (∀ p N, p.Prime → 1 ≤ N → f (p * N) * f (p * N + p) = f N * f (N + 1))
      ↔ (∀ a b, 1 ≤ a → 1 ≤ b → f (a * b) = f a * f b) := by sorry

end MultiplicativeFunctions
