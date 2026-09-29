-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_matching_concentration
-- name    : FranklKupavskii2022.EMC.matching_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:19:45.850228+00:00
-- url     : https://prove2.me/theorems/a979079e-04fe-4afb-b4a5-23a6fd849a22
-- title:
--   Theorem 12: $\Pr[|\eta-\alpha t|\ge2\beta\sqrt t]\le2e^{-\beta^2/2}$
-- statement:
--   Let $m,l,t$ be integers with $t\ge1$ and $m\ge tl$, let $\mathcal G\subseteq\binom{[m]}{l}$ with density $\alpha=|\mathcal G|/\binom ml$, and let $\eta=|\mathcal G\cap\mathcal B|$ for a uniformly random $t$-matching $\mathcal B$ of $l$-sets in $[m]$. Then for every $\beta>0$
--
--   $$
--   \Pr\big[|\eta-\alpha t|\ge2\beta\sqrt t\big]\le2e^{-\beta^2/2}. \tag{21}
--   $$
--
--   The number of members of a fixed family hit by a random matching is therefore concentrated around its mean $\alpha t$ with Gaussian tails, uniformly in $m$ and $l$. This is the paper's main probabilistic tool and is of independent interest.
--
--   **Formalization Note** $t\ge1$ is included; for $t=0$ the event is certain and (21) fails for large $\beta$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Theorem 12, p. 7 (setting of Lemma 10, p. 6)

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_tMatchings

namespace FranklKupavskii2022.EMC

/-- Theorem 12 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 7): in the setting of Lemma 10 (`m ≥ tl`,
`G ⊂ \binom{[m]}{l}`, `α := |G|/\binom{m}{l}`, `η = |G ∩ B|` for a uniformly random `t`-matching
`B` of `l`-sets, any positive `β`),
`Pr[|η − αt| ≥ 2β√t] ≤ 2e^{−β²/2}` (21).

**Formalization Note.** `B` is uniform on `tMatchings m l t` (ordered `t`-tuples of pairwise
disjoint `l`-subsets of `[m]`), nonempty since `t * l ≤ m`. `1 ≤ t` is added: at `t = 0` the event
`|0 − 0| ≥ 0` is certain and (21) fails for large `β`; the paper's `t`-matchings have `t ≥ 1`.
`β > 0` is Lemma 10's "for any positive β". -/
theorem matching_concentration (m l t : ℕ) (ht : 1 ≤ t) (hm : t * l ≤ m) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard l) (β : ℝ) (hβ : 0 < β) :
    prob m l t (fun B => 2 * β * Real.sqrt t ≤ |(eta G B : ℝ) - density m l G * t|) ≤
      2 * Real.exp (-(β ^ 2) / 2) := by sorry

end FranklKupavskii2022.EMC
