-- Prove2me | Theorems.Thm_MomentSearch_midpoint_nodal_gamma_identities
-- name    : MomentSearch.midpoint_nodal_gamma_identities
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:25:05.816205+00:00
-- url     : https://prove2.me/theorems/e2cf58eb-e110-45b2-ad01-93bd61ad8004
-- title:
--   Gamma identities for the midpoint nodal polynomial
-- statement:
--   For the $N$ midpoint nodes, set $u=N(1+x)/2$, $v=N(1-x)/2$, and let $T$ be the monic polynomial vanishing at those nodes. On $[-1,1]$,
--   $$
--   |T(x)|=G(x)|\cos(\pi u)|,\qquad
--   G(x)=\frac{(2/N)^N}{\pi}\Gamma(u+1/2)\Gamma(v+1/2).
--   $$
--   At the $j$-th node, $|T'(\zeta_j)|=(\pi N/2)G(\zeta_j)$. For the first identity, write $T(x)=(2/N)^N\prod_{j=1}^N(u-j+1/2)$ and use the Gamma recurrence and reflection formula off the nodes. At the nodes both sides vanish. For the derivative, the product with its $j$-th factor omitted has absolute value $(2/N)^{N-1}(j-1)!(N-j)!$.
-- source:
--   Rakhmanov, Bounds for polynomials with a unit discrete norm, §2.1, (2.3) and (2.6), https://annals.math.princeton.edu/2007/165-1/p03. This is the alternative Gamma expression derived from the recurrence and reflection identities in NIST DLMF §5.5, https://dlmf.nist.gov/5.5.

import Mathlib

theorem MomentSearch.midpoint_nodal_gamma_identities (N : ℕ) (hN : 0 < N) :
    let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
    let T := Lagrange.nodal (Finset.Icc 1 N) ζ
    let b : ℝ := Real.pi * N / 2
    let G : ℝ → ℝ := fun x =>
      (2 / (N : ℝ)) ^ N / Real.pi *
        (Real.Gamma ((N : ℝ) / 2 * (1 + x) + 1 / 2) *
          Real.Gamma ((N : ℝ) / 2 * (1 - x) + 1 / 2))
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |T.eval x| = G x * |Real.cos (b * (x + 1))|) ∧
    (∀ j ∈ Finset.Icc 1 N, |T.derivative.eval (ζ j)| = G (ζ j) * b) := by sorry
