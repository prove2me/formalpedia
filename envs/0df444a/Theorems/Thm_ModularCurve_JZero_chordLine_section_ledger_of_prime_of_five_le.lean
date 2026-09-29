-- Prove2me | Theorems.Thm_ModularCurve_JZero_chordLine_section_ledger_of_prime_of_five_le
-- name    : ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/48ef33c2-0142-5a86-8e87-ce0e91cd36cb
-- title:
--   Chord-line height identity for sections on X₀(N), N≥ 5 prime
-- statement:
--   Let $N$ be a prime with $N\ge 5$, and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$, viewed as a field of Laurent series, with places in the sense of the project (valuation subrings containing $\overline{\mathbb Q}$, proper, with principal ideals) and $\bar\infty =$ `cuspInftyBar N` the place attached to the $q$-expansion at infinity. Let $E =$ `embDivisor N` be the divisor `embDegree N` $\cdot\,\bar\infty$, and let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space $L(E) = \{f : v(f)\le \exp(E_v)\ \forall v\}$. Then there is a real $C\ge 0$, depending only on $N$ and $s$, such that for every $k\in\mathbb N$, every nonzero $u \in L(kE)$, every divisor $B$ with $B_w = \operatorname{ord}_w u + k E_w$ for all places $w$, and every place $v\ne\bar\infty$ with $B_v = 0$, the quantity $$\Big|\sum_{w} B_w\big(h(G_w(v)) - h(G_w(\bar\infty))\big) + B_{\bar\infty}\, h(\xi(v,\bar\infty)) - k\,(\deg E - 1)\, h(x_v)\Big|$$ is at most $C(k+1)$. Here the sum runs over the support of $B$ with $v$ and $\bar\infty$ deleted; $x_v =$ `evalVec s v` is the evaluation vector $i \mapsto v.\mathrm{evalAt}(s_i\, s_{i_v}^{-1})$ at a pivot index $i_v$; $G_w(v)$ is the tuple $(i,j)\mapsto w.\mathrm{evalAt}(x_{v,i}\, s_j - x_{v,j}\, s_i)$; $\xi(v,\bar\infty) =$ `chordVec s v` $\bar\infty$ is the tuple $(i,j)\mapsto x_{v,i}x_{\bar\infty,j} - x_{v,j}x_{\bar\infty,i}$; $h =$ `absLogHeight` is the logarithmic height of a tuple of algebraic numbers, normalised by the degree of the field they generate; $\deg E$ is the sum of the coefficients of $E$; and $h(x_v) =$ `pointHt s v`.
--
--   This is the global form of the chord-line height identity for sections of multiples of the embedding divisor: summing the place-by-place Jensen formulas (Gauss's lemma at the finite places of good reduction, a bounded defect at the finitely many remaining finite places, and the archimedean Jensen estimate) over all places of a number field containing the relevant coordinates leaves an error linear in $k$. It is the form from which [`ModularCurve.JZero.chordLine_core_of_prime_of_five_le`](thm.html#ModularCurve.JZero.chordLine_core_of_prime_of_five_le) extracts the chord-line comparison of heights on the projective model of $X_0(N)$ determined by the basis $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_chordLine_section_ledger_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.chordLine_section_ledger_of_prime_of_five_le (N : ℕ) [NeZero N]
    (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        B v = 0 → v ≠ cuspInftyBar N →
        |(((B.erase v).erase (cuspInftyBar N)).sum fun w m => (m : ℝ) *
            (absLogHeight (fun p : Fin r × Fin r =>
                w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
              - absLogHeight (fun p : Fin r × Fin r =>
                  w.evalAt (evalVec s (cuspInftyBar N) p.1 • s p.2
                    - evalVec s (cuspInftyBar N) p.2 • s p.1))))
          + ((B.erase v) (cuspInftyBar N) : ℝ) * absLogHeight (chordVec s v (cuspInftyBar N))
          - (k : ℝ) * (((embDivisor N).sum fun _ m => (m : ℝ)) - 1) * pointHt s v|
        ≤ C * (k + 1) := by sorry
