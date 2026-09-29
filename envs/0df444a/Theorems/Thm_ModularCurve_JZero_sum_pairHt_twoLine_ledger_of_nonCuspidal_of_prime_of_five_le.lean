-- Prove2me | Theorems.Thm_ModularCurve_JZero_sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le
-- name    : ModularCurve.JZero.sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/865892ed-5fe6-5a23-a7bd-ed0077008540
-- title:
--   Two-line height identity at non-cuspidal base places, prime level ≥ 5
-- statement:
--   Let $N$ be a prime with $5 \le N$, and let $s : \mathrm{Fin}\,r \to \bar F_N$ be a family in the base-changed modular function field $\bar F_N =$ `modularFunctionFieldBar N` which is an embedding basis: $s$ is linearly independent over $\overline{\mathbb Q}$ and its span is the Riemann–Roch space of the divisor `embDivisor N` $= \mathrm{embDegree}(N)\cdot[\bar\infty]$, where $\bar\infty =$ `cuspInftyBar N`. Then there are real constants $c_0, C_0$ with the following property. Let $k \in \mathbb N$ and let $u \ne 0$ lie in the Riemann–Roch space of $k\cdot$`embDivisor N`, let $B$ be the divisor with $B(w) = \mathrm{ord}_w(u) + k\cdot(\mathrm{embDivisor}\,N)(w)$ for every place $w$ of $\bar F_N$ over $\overline{\mathbb Q}$, and let $v_0$ be a place which is either $\bar\infty$ or is such that the element of $\bar F_N$ given by the coefficientwise image of the $q$-expansion `jq` lies in the valuation subring of $v_0$. Let $t, t' \in \bar F_N$ satisfy $\mathrm{ord}_{v_0}(t) = 1$ whenever $B(v_0) > 0$, and $\mathrm{ord}_{\bar\infty}(t') = 1$ whenever $B(\bar\infty) > 0$. Then the absolute value of $$\Big(\sum_{w \ne v_0} B(w)\,\Lambda(v_0,w) - \sum_{w \ne \bar\infty} B(w)\,\Lambda(\bar\infty,w)\Big) - \Big(\big[(k - 2B(v_0))\,\mathrm{pt}(v_0) + B(v_0)\,h(y_{v_0,t})\big] - \big[(k - 2B(\bar\infty))\,\mathrm{pt}(\bar\infty) + B(\bar\infty)\,h(y_{\bar\infty,t'})\big]\Big)$$ is at most $c_0 k + C_0$. Here the sums run over the supports of $B$ with the indicated place erased, weighted by the integers $B(w)$; $\mathrm{pt}(v) =$ `pointHt s v` is the normalised absolute logarithmic height `absLogHeight` of the normalised evaluation vector `evalVec s v`, whose $i$-th entry is the value at $v$ of $s_i/s_{\mathrm{pivotIndex}}$; $\Lambda(v,w) =$ `pairHt s v w` $= \mathrm{pt}(v) + \mathrm{pt}(w) -$ `absLogHeight (chordVec s v w)`; and $h(y_{v,t})$ is `absLogHeight` of the family indexed by pairs $(i,j)$ whose $(i,j)$-entry is `regVal s v t 1 1` applied to $\mathrm{evalVec}(v)_i\, s_j - \mathrm{evalVec}(v)_j\, s_i$, i.e. the value at $v$ of that element divided by $s_{\mathrm{pivotIndex}}$ and by $t$.
--
--   This is the two-line form of the global height accounting (an arithmetic Jensen-type identity, valid up to an error $O(k)$) for the curve attached to $X_0(N)$, in the edition where the base place $v_0$ is restricted to be either the cusp $\bar\infty$ or a place at which the modular function $j$ is integral; the error is uniform in the section $u$ and grows at most linearly in $k$. It is assembled from the good-place, bad-place and non-cuspidal archimedean Jensen estimates together with Riemann–Roch data for $\bar F_N$, and it is used in the self-adjunction estimate for chord divisors, [`ModularCurve.JZero.pairing_chord_self_le_of_prime_of_five_le`](thm.html#ModularCurve.JZero.pairing_chord_self_le_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JZero.sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ C₀ : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (v₀ = cuspInftyBar N ∨
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) ∈ v₀.toValuationSubring) →
      ∀ (t t' : modularFunctionFieldBar N),
        (0 < B v₀ → v₀.ord t = 1) → (0 < B (cuspInftyBar N) → (cuspInftyBar N).ord t' = 1) →
        |(((B.erase v₀).sum fun w n => (n : ℝ) * pairHt s v₀ w)
            - ((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * pairHt s (cuspInftyBar N) w))
          - ((((k : ℝ) - 2 * (B v₀ : ℝ)) * pointHt s v₀
              + (B v₀ : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                  regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)))
            - (((k : ℝ) - 2 * (B (cuspInftyBar N) : ℝ)) * pointHt s (cuspInftyBar N)
              + (B (cuspInftyBar N) : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                  regVal s (cuspInftyBar N) t' 1 1
                    (evalVec s (cuspInftyBar N) p.1 • s p.2 - evalVec s (cuspInftyBar N) p.2 • s p.1))))|
          ≤ c₀ * k + C₀ := by sorry
