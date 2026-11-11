-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_contrast_only_estimate
-- name    : MinimaxInterventions1429.Separable.contrast_only_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:11.096115+00:00
-- url     : https://prove2.me/theorems/d29f89a8-130b-4947-b2ac-3b644d339e9d
-- title:
--   Proposition 3.7 — contrast-only estimate
-- statement:
--   Let $m,k\ge2$, $L\in[0,1]^{m\times k}$, $\alpha\ge0$, and integer $T\ge1$. Let $\widehat\omega$ be the actual contrast phase of the Section 3.2 reconstruction. If its $m(k-1)T$ realized bit answers are $\alpha$-accurate, the table
--
--   $$\widehat L_{gh}=\tfrac12+\widehat\omega_{gh}
--   -\tfrac12\bigl(\max_j\widehat\omega_{gj}+\min_j\widehat\omega_{gj}\bigr),\qquad
--   d_q(\widehat L,L)\le\rho(L)+4\alpha+2^{1-T},$$
--
--   has each estimated row's midrange equal to $1/2$. Here $\rho(L)=\tfrac14\max_{g\ne r}(2-\operatorname{span}_g(L)-\operatorname{span}_r(L))$. The statement verifies the exact contrast query count and that this phase is the prefix of the same reconstruction run, for every history-dependent oracle. It requires no interaction lower bound. The estimator is a real table and is not clipped to the unit cube when noisy estimated row spans exceed one.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: adversarial bit answers accurate only along the realized calls → a finite bit-query program evaluated with an arbitrary history-dependent oracle and a witness for each recorded bit; reason: the program observes only bits and public queries; weak ties admit both bits and no common witness or numerical response is assumed
--   - encoding: the first m(k-1)T calls of the reconstruction → the contrast-phase program has this exact depth and its history is a prefix of the same reconstruction run; reason: this identifies the actual shared query prefix; 2 times eta T is exactly 2 to the power 1-T
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Proposition 3.7, printed p.13 (PDF p.15)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem contrast_only_estimate {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (L : Table m k) (hL : InCube L)
    (α : ℝ) (hα : 0 ≤ α) (T : ℕ) (hT : 1 ≤ T) :
    (contrastPhase m k α T).maxQueries = m * (k - 1) * T ∧
    (∀ O : BitOracle m k,
      AccurateHistory L α ((contrastPhase m k α T).run O []).2 →
      quotientDist ((contrastEstimate m k α T).run O []).1 L ≤
        ambiguityRadius L + 4 * α + 2 * eta T) ∧
    (∀ O : BitOracle m k,
      (((contrastPhase m k α T).run O []).2).IsPrefix
        (((reconstruction m k α T).run O []).2)) := by sorry

end MinimaxInterventions1429.Separable
