-- Prove2me | Theorems.Thm_MultiplicativeFunctions_collapse_forces_completelyMult
-- name    : MultiplicativeFunctions.collapse_forces_completelyMult
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:26:15.163452+00:00
-- url     : https://prove2.me/theorems/1580b527-ec30-441d-a938-2218740f8b37
-- title:
--   The shift relation forces complete multiplicativity
-- statement:
--   **A $\pm1$-valued function whose consecutive-pair correlation is prime-dilation invariant is
--   completely multiplicative.**
--
--   Let $f : \mathbb{N} \to \mathbb{R}$ satisfy $f(n) = \pm1$ for $n \ge 1$, $f(1) = 1$, and the
--   **collapse relation**: for every prime $p$ and every $N \ge 1$,
--
--   $$f(pN)\,f(pN+p) \;=\; f(N)\,f(N+1).$$
--
--   Then $f$ is completely multiplicative: $f(ab) = f(a)f(b)$ for all $a,b \ge 1$.
--
--   This is the substantial direction of the characterisation. The hypothesis constrains only the
--   two-point correlation $f(n)f(n+1)$, and only under dilation by a prime — on its face far weaker
--   than multiplicativity, which constrains $f$ at every pair of arguments. The conclusion says the
--   two are equivalent for $\pm1$-valued functions.
--
--   The relevance is to the Chowla and Erd\H{o}s-discrepancy circle of problems, where the
--   two-point correlation is the object of study and the collapse relation arises naturally when
--   manipulating it. The theorem shows the hypothesis cannot be exploited as a genuine weakening:
--   any $\pm1$ function satisfying it is completely multiplicative, hence (being $\pm1$-valued)
--   determined by its values at the primes, essentially a real character.
--
--   **Formalization note.** No multiplicativity is assumed; `hpm` and `h1` fix $f$ to be
--   $\pm1$-valued and normalised, and `hcol` is the only structural hypothesis.
-- source:
--   Arising in the Chowla / Erdős-discrepancy circle; cf. Tao, *The Erdős discrepancy problem* (2016). Lean proof extracted from `Salt/Entropy/Chowla/BoundaryMap.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace MultiplicativeFunctions

theorem collapse_forces_completelyMult (f : ℕ → ℝ)
    (hpm : ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1) (h1 : f 1 = 1)
    (hcol : ∀ p N, p.Prime → 1 ≤ N → f (p * N) * f (p * N + p) = f N * f (N + 1)) :
    ∀ a b, 1 ≤ a → 1 ≤ b → f (a * b) = f a * f b := by sorry

end MultiplicativeFunctions
