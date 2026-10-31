-- Prove2me | Theorems.Thm_NestedCRP_level_conditional
-- name    : NestedCRP.level_conditional
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:51.019685+00:00
-- url     : https://prove2.me/theorems/41488c07-3e89-49ff-8b96-61a3cf7b245d
-- title:
--   Level conditional, Eq. (2)
-- statement:
--   Fix a state and a site $s_0$. The level weights $\mathrm{levelWeight}(k)$ are positive and summable with positive total, and for all levels $k,k'$,
--
--   $$
--   \mathrm{joint}\bigl(z[s_0\mapsto k]\bigr)\,\mathrm{levelWeight}(k')=\mathrm{joint}\bigl(z[s_0\mapsto k']\bigr)\,\mathrm{levelWeight}(k).
--   $$
--
--   So the full conditional of $z_{d,n}$ given everything else is the level prior of §5.1 times the normalized word predictive. This is the distribution step (b) of the sampler draws from.
--
--   Differences from the source:
--   - reading: Eq. (2) with the second factor as printed in Eq. (3) → the second factor is the normalized predictive; reason: the only reading under which Eq. (2) holds; see word_predictive
--   - reading: Eq. (2) writes ∝ with no normalizing claim → the weights are positive and summable with positive total; reason: ∝ over infinitely many levels presupposes a finite positive normalizer
--   - encoding: proportionality → a cross-multiplied identity over pairs of levels; reason: equivalent since the weights are positive
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, Eq. (2), p.7:16

import Mathlib
import Definitions.Def_NestedCRP_levelWeight
import Definitions.Def_NestedCRP_posterior

namespace NestedCRP

/-- Eq. (2): as a function of the level of site `s₀`, the joint is proportional to the level weight.
The weights are positive and summable with positive total, so the conditional law they define
exists. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (2), p.7:16. -/
theorem level_conditional {V D : ℕ} (H : Hyper) (C : Corpus V D) (x : C.State) (s₀ : C.Site) :
    (∀ k, 0 < levelWeight H C x s₀ k) ∧ Summable (levelWeight H C x s₀) ∧
      0 < ∑' k, levelWeight H C x s₀ k ∧
      ∀ k k', joint H C (x.1, C.setLevel x.2 s₀ k) * levelWeight H C x s₀ k' =
        joint H C (x.1, C.setLevel x.2 s₀ k') * levelWeight H C x s₀ k := by sorry

end NestedCRP
