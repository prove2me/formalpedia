-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_indicator_covariance_bound
-- name    : FranklKupavskii2022.EMC.indicator_covariance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:19:12.978253+00:00
-- url     : https://prove2.me/theorems/fa73756c-2c59-4919-a7a0-5c1165f76f00
-- title:
--   Proposition 11: $|\mathrm{Cov}[\eta_i,\eta_j]|\le\frac{\alpha(1-\alpha)}{t-1}$
-- statement:
--   Let $m,l,t$ be integers with $m\ge tl$, let $\mathcal G\subseteq\binom{[m]}{l}$, $\alpha=|\mathcal G|/\binom ml$, and let $\mathcal B=(B_1,\dots,B_t)$ be a uniformly random $t$-matching of $l$-sets in $[m]$. With $\eta_i=\mathbf 1[B_i\in\mathcal G]$, for any $i\ne j$ in $[t]$
--
--   $$
--   \big|\mathrm{Cov}[\eta_i,\eta_j]\big|\le\frac{\alpha(1-\alpha)}{t-1}.
--   $$
--
--   The bound comes from the spectrum of the Kneser graph and gives $\mathrm{Var}[\eta]\le2t\alpha(1-\alpha)$, the Chebyshev-type concentration of Lemma 10.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Proposition 11, p. 6 (setting of Lemma 10)

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_tMatchings

namespace FranklKupavskii2022.EMC

/-- Proposition 11 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 6): in the setting of Lemma 10
(`m ≥ tl`, `G ⊂ \binom{[m]}{l}`, `α := |G|/\binom{m}{l}`, `B` a uniformly random `t`-matching of
`l`-sets, `η_i` the indicator that the `i`-th set of `B` lies in `G`), for any `i, j ∈ [t]` with
`i ≠ j` we have `|Cov[η_i, η_j]| ≤ \frac{α(1−α)}{t−1}`.

**Formalization Note.** Positions are `Fin t`; `i ≠ j` forces `t ≥ 2`, so `t − 1 > 0` in `ℝ`. The
covariance is taken under the uniform distribution on `tMatchings m l t` (ordered `t`-tuples of
pairwise disjoint `l`-subsets of `[m]`), which is nonempty because `t * l ≤ m`. -/
theorem indicator_covariance_bound (m l t : ℕ) (hm : t * l ≤ m) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard l) (i j : Fin t) (hij : i ≠ j) :
    |cov m l t (etaI G i) (etaI G j)| ≤
      density m l G * (1 - density m l G) / ((t : ℝ) - 1) := by sorry

end FranklKupavskii2022.EMC
