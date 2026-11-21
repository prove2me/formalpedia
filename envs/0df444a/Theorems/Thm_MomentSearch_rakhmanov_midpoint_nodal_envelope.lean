-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_midpoint_nodal_envelope
-- name    : MomentSearch.rakhmanov_midpoint_nodal_envelope
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:19:50.042821+00:00
-- url     : https://prove2.me/theorems/731ed2e4-df4e-4900-a367-e823247ce741
-- title:
--   Rakhmanov’s midpoint nodal envelope and derivative bound
-- statement:
--   For $N\ge1$ let $T$ be the monic nodal polynomial of the midpoint grid, $b=\pi N/2$, and $w(z)=\exp(V_1(z)-N)$ for the uniform logarithmic potential $V_1$ of (2.1). The Lean statement uses the explicit elementary formula for $w$.
--
--   There is a scale $c>0$ for each $N$ such that
--   $$
--    |T(x)|\le \frac{2c}{w(x)}|\cos(b(x+1))|\quad(-1\le x\le1),
--    \qquad |T'(\zeta_j)|\ge \frac{cb}{w(\zeta_j)}.
--   $$
--   This is the upper envelope in Lemma 1 and the lower envelope at the nodes from (2.6), with $c=e^{-N}\min C_1$. The phase can be written with $x+1$ because $b(1-x)+b(x+1)=N\pi$ and the absolute value of cosine is unchanged by this reflection.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Ann. of Math. 165 (2007), 55–88, §2.1, Lemma 1 and (2.1), (2.4)–(2.6), p. 63; proof in §3.2. https://annals.math.princeton.edu/2007/165-1/p03

import Mathlib

theorem MomentSearch.rakhmanov_midpoint_nodal_envelope :
    ∀ N : ℕ, 0 < N →
      let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
      let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
        ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
      let T := Lagrange.nodal (Finset.Icc 1 N) ζ
      let b : ℝ := Real.pi * N / 2
      ∃ c : ℝ, 0 < c ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          |T.eval x| ≤ 2 * c * |Real.cos (b * (x + 1))| / w x) ∧
        (∀ j ∈ Finset.Icc 1 N,
          c * b / w (ζ j) ≤ |T.derivative.eval (ζ j)|) := by sorry
