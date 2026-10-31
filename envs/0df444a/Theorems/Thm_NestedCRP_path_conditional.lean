-- Prove2me | Theorems.Thm_NestedCRP_path_conditional
-- name    : NestedCRP.path_conditional
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:37.056986+00:00
-- url     : https://prove2.me/theorems/3a1bb223-2fdd-409d-940b-af8f7cc0cb24
-- title:
--   Path conditional, Eq. (4)
-- statement:
--   Fix level allocations, a document $d$ and a tree $T_0$. The path weights are positive and, over the trees $T'$ with the same restriction to the other documents as $T_0$, summable with positive total. For trees $T,T'$ with the same restriction to the other documents,
--
--   $$
--   \mathrm{joint}(T,z)\,\mathrm{pathWeight}(T')=\mathrm{joint}(T',z)\,\mathrm{pathWeight}(T).
--   $$
--
--   So the full conditional of the path of $d$ is the prior on paths times the word likelihood. This is the distribution step (a) of the sampler draws from.
--
--   Differences from the source:
--   - reading: §5.2 is "only concerned with paths" of length max(z_d) → the conditional of the whole tree; the truncated form is the separate theorem path_conditional_truncated; reason: §5.1 can raise a level past that length and the paper does not say how to extend a path; keeping the whole tree avoids this, and summing the tails recovers the printed form
--   - encoding: labelled paths c_d conditioned on labelled c_{-d} → trees with a given restriction to the other documents; reason: conditioning on labels would reveal the position of d
--   - reading: Eq. (4) writes ∝ with no normalizing claim → the weights are positive and summable with positive total; reason: ∝ over infinitely many trees presupposes a finite positive normalizer
--   - encoding: proportionality → a cross-multiplied identity over pairs of trees; reason: equivalent since the weights are positive
--   - encoding: a vocabulary of V words, nonempty implicitly → [NeZero V], that is V ≥ 1; reason: nondegeneracy only: at V = 0 the symmetric Dirichlet on the empty simplex is undefined and the Γ(Vη) = Γ(0) factors of the path weights are poles; no instance of the source is excluded
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, Eq. (4), p.7:17

import Mathlib
import Definitions.Def_NestedCRP_pathWeight
import Definitions.Def_NestedCRP_posterior

namespace NestedCRP

/-- Eq. (4): as a function of the path of document `d`, that is, over the trees with a given
restriction to the other documents, the joint is proportional to the path weight. The weights are
positive and summable with positive total, so the conditional law they define exists.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), Eq. (4), p.7:17. -/
theorem path_conditional {V D : ℕ} [NeZero V] (H : Hyper) (C : Corpus V D) (z : C.Levels)
    (d : Fin D) (T₀ : Tree D) :
    (∀ T', 0 < pathWeight H C z d T') ∧
      Summable (fun T' : {T' : Tree D // T₀.AgreesOff d T'} => pathWeight H C z d T'.1) ∧
      0 < ∑' T' : {T' : Tree D // T₀.AgreesOff d T'}, pathWeight H C z d T'.1 ∧
      ∀ T T' : Tree D, T.AgreesOff d T' →
        joint H C (T, z) * pathWeight H C z d T' = joint H C (T', z) * pathWeight H C z d T := by sorry

end NestedCRP
