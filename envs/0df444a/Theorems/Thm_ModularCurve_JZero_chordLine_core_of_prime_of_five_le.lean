-- Prove2me | Theorems.Thm_ModularCurve_JZero_chordLine_core_of_prime_of_five_le
-- name    : ModularCurve.JZero.chordLine_core_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/eb3c6c21-fc87-5ba0-8ac5-c12e0ea11d0e
-- title:
--   Chord-height comparison bounded by divisor mass, prime level
-- statement:
--   Let $N$ be a prime with $5 \le N$, and let $\overline F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, regarded as an extension of $\overline{\mathbb Q}$; places are valuation subrings of $\overline F_N$ containing $\overline{\mathbb Q}$, proper and principal, with $\mathrm{ord}_v$ the associated normalised valuation and $\mathrm{eval}_v$ the residue value pulled back to $\overline{\mathbb Q}$. Let $s = (s_i)_{i < r}$ be a family in $\overline F_N$ satisfying `IsEmbBasis N s`, i.e. linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space of `embDivisor N`. The assertion is that there exists a real constant $c$ such that for every $f \neq 0$ in $\overline F_N$, every finitely supported divisor $A$ with $A(w) = \mathrm{ord}_w(f)$ at all places $w$, and every place $v$ with $A(v) = 0$, the absolute value of $$\sum_{w} A(w)\bigl(h_w(v) - h_w(\overline\infty)\bigr) \;+\; A(\overline\infty)\,\mathrm{absLogHeight}(\mathrm{chordVec}\,s\,v\,\overline\infty)$$ is at most $c \sum_w |A(w)|$. Here $\overline\infty$ is `cuspInftyBar N`, the first sum runs over the support of $A$ with $v$ and $\overline\infty$ deleted, the coefficient $A(\overline\infty)$ is taken after deleting $v$ (hence is $0$ when $v = \overline\infty$), and $h_w(u) = \mathrm{absLogHeight}\bigl(p \mapsto \mathrm{eval}_w(\mathrm{evalVec}(s,u)_{p_1} s_{p_2} - \mathrm{evalVec}(s,u)_{p_2} s_{p_1})\bigr)$ is the absolute logarithmic height, indexed by pairs $p \in \mathrm{Fin}\,r \times \mathrm{Fin}\,r$, of the values at $w$ of the chord functions of $s$ at $u$, with $\mathrm{evalVec}$ the pivot-normalised evaluation of $s$ at $u$.
--
--   This is the height-theoretic core of a Néron-type estimate on the modular curve of level $N$: the place-by-place comparison of chord heights against a principal divisor is controlled linearly by the mass $\sum_w |A(w)|$ of that divisor. It is assembled from the quotient-representation lemma [`ModularCurve.JZero.quot_rep`](thm.html#ModularCurve.JZero.quot_rep) together with the corresponding bound for nonzero sections of Riemann–Roch spaces of integer multiples of the embedding divisor, and is used in turn by [`ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le`](thm.html#ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le) to bound the chord pairing on principal divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_chordLine_core_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.chordLine_core_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c : ℝ, ∀ (f : modularFunctionFieldBar N)
      (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      f ≠ 0 → (∀ w, A w = w.ord f) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), A v = 0 →
        |(((A.erase v).erase (cuspInftyBar N)).sum fun w m => (m : ℝ) *
            (absLogHeight (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
              - absLogHeight (fun p : Fin r × Fin r =>
                  w.evalAt (evalVec s (cuspInftyBar N) p.1 • s p.2 - evalVec s (cuspInftyBar N) p.2 • s p.1))))
          + ((A.erase v) (cuspInftyBar N) : ℝ)
              * absLogHeight (chordVec s v (cuspInftyBar N))|
        ≤ c * (A.sum fun _ m => |(m : ℝ)|) := by sorry
