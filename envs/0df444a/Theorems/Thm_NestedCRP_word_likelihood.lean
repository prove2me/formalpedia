-- Prove2me | Theorems.Thm_NestedCRP_word_likelihood
-- name    : NestedCRP.word_likelihood
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:45.084245+00:00
-- url     : https://prove2.me/theorems/bfb8f4c4-b897-46fc-bc07-35af12749488
-- title:
--   Word likelihood $p(w_d\mid c,w_{-d},z,\eta)$
-- statement:
--   Fix a tree, level allocations and a document $d$. Then
--
--   $$
--   \mathrm{topic}(T,z)=\Bigl(\prod_{\ell\le\max(z_d)}R_\ell\Bigr)\;\mathrm{topic}_{-d}(T,z),
--   $$
--
--   where $\mathrm{topic}_{-d}$ is the probability of the words of the other documents and
--
--   $$
--   R_\ell=\frac{\Gamma\bigl(\sum_v N^-(v)+V\eta\bigr)}{\prod_v\Gamma\bigl(N^-(v)+\eta\bigr)}\cdot\frac{\prod_v\Gamma\bigl(N(v)+\eta\bigr)}{\Gamma\bigl(\sum_v N(v)+V\eta\bigr)}.
--   $$
--
--   Here $N$ and $N^-$ count the words in the node of $d$ at level $\ell$, with and without those of $d$. This is the likelihood factor of Eq. (4).
--
--   Differences from the source:
--   - encoding: the conditional p(w_d | c, w_{-d}, z, η) → a product identity between word masses; reason: equivalent to the conditional, and needs no division
--   - encoding: levels and sticks are 1-based → levels and sticks are 0-based; reason: Lean indexing; level ℓ here is the paper's level ℓ + 1, and no instance changes
--   - encoding: a vocabulary of V words, nonempty implicitly → [NeZero V], that is V ≥ 1; reason: nondegeneracy only: at V = 0 the symmetric Dirichlet on the empty simplex is undefined and the Γ(Vη) = Γ(0) factors of the path weights are poles; no instance of the source is excluded
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.2, second display, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_pathWeight
import Definitions.Def_NestedCRP_topicMass

namespace NestedCRP

/-- The likelihood `p(w_d | c, w_{-d}, z, η)` of §5.2: the probability of the corpus is the product
over the levels up to `max(z_d)` of the ratios of Dirichlet normalizers, times the probability of
the words of the other documents. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, second display, p.7:17. -/
theorem word_likelihood {V D : ℕ} [NeZero V] (H : Hyper) (C : Corpus V D) (T : Tree D)
    (z : C.Levels) (d : Fin D) :
    topicMass H.eta C T z =
      (∏ ℓ ∈ Finset.range (Finset.univ.sup (z d) + 1), levelRatio H.eta C z T d ℓ) *
        topicMassOn H.eta C T z (Finset.univ.filter fun s => s.1 ≠ d) := by sorry

end NestedCRP
