-- Prove2me | Theorems.Thm_NestedCRP_word_predictive
-- name    : NestedCRP.word_predictive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:52.879978+00:00
-- url     : https://prove2.me/theorems/94273ee3-3622-49e3-873b-24937b5fcdf9
-- title:
--   Word predictive of Eq. (3), normalized
-- statement:
--   Fix a tree, level allocations, a site $s_0$ and a level $k$. The probability of the corpus with $s_0$ at level $k$ equals the probability of the other words times the predictive
--
--   $$
--   \frac{C_k(w_{s_0})+\eta}{\sum_v C_k(v)+V\eta},
--   $$
--
--   where $C_k(v)$ counts the other words with level $k$, in the node of the document of $s_0$ at level $k$, equal to $v$.
--
--   This is the smoothed frequency of the word in the topic at that level of the path, and the second factor of Eq. (2).
--
--   Differences from the source:
--   - reading: Eq. (3): the predictive is ∝ the count plus η → the normalized predictive (count + η) / (total + Vη); reason: Eq. (3) is ∝ in the word; the denominator depends on the level, and Eq. (2) needs the level likelihood (with one document, words (a,b), b at the first level, V = 2, η = ½, the numerators are ½ at both levels and the likelihoods ¼ and ½). Eq. (6) prints this form
--   - encoding: p(w_{d,n} | z, c, w_{-(d,n)}, η) → a product identity between word masses; reason: equivalent to the conditional, and needs no division
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, Eq. (3), p.7:16

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_levelWeight
import Definitions.Def_NestedCRP_topicMass

namespace NestedCRP

/-- The word predictive: the probability of the corpus with site `s₀` at level `k` is the normalized
predictive of Eq. (3) times the probability of the other words.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (3), p.7:16. -/
theorem word_predictive {V D : ℕ} (H : Hyper) (C : Corpus V D) (T : Tree D) (z : C.Levels)
    (s₀ : C.Site) (k : ℕ) :
    topicMass H.eta C T (C.setLevel z s₀ k) =
      levelLik H.eta C (T, z) s₀ k * topicMassOn H.eta C T z (Finset.univ.erase s₀) := by sorry

end NestedCRP
