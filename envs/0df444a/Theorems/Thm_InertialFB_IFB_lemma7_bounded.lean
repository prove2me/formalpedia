-- Prove2me | Theorems.Thm_InertialFB_IFB_lemma7_bounded
-- name    : InertialFB.IFB.lemma7_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:52:51.306174+00:00
-- url     : https://prove2.me/theorems/ee0bd3e5-37b2-419b-9e34-4ddec644cf0e
-- title:
--   Lemma 7: $p_k - \omega p_{k-1} \le K$ with $\omega < 1$ forces boundedness
-- statement:
--   Let $(p_k)$ be a nonnegative real sequence, and let $\omega < 1$ and $K \in \mathbb R$. Suppose that
--   $$p_k - \omega\,p_{k-1} \le K \qquad \text{for all sufficiently large } k.$$
--   Then $(p_k)$ is bounded.
--
--   The paper applies this with $p_k = \|u_k - q\|^2$, $q \in \mathcal S$, to show that the IFB iterates are bounded when $\Theta$ has a minimizer.
--
--   **Formalization Note** "For all sufficiently large $k$" is written with the shifted index, $p_{k+1} - \omega p_k \le K$ eventually, which avoids natural-number subtraction. "Bounded" is stated as bounded above and bounded below (the latter is immediate from nonnegativity).
-- source:
--   Attouch, Peypouquet & Redont, A Dynamical Approach to an Inertial Forward-Backward Algorithm for Convex Minimization, authors' manuscript (Aug 2013) of SIAM J. Optim. (2014), DOI 10.1137/130910294, p. 10, Lemma 7

import Mathlib

open Filter

namespace InertialFB.IFB

/-- **Lemma 7** (Attouch–Peypouquet–Redont, p. 10). Let `(p_k)` be a nonnegative real sequence
such that `p_k - ω p_{k-1} ≤ K` for some `ω < 1`, some `K ∈ ℝ` and all sufficiently large `k`
(written with the shifted index: `p_{k+1} - ω p_k ≤ K` eventually). Then `(p_k)` is bounded. -/
theorem lemma7_bounded (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (ω K : ℝ) (hω : ω < 1)
    (h : ∀ᶠ k in atTop, p (k + 1) - ω * p k ≤ K) :
    BddAbove (Set.range p) ∧ BddBelow (Set.range p) := by sorry

end InertialFB.IFB
