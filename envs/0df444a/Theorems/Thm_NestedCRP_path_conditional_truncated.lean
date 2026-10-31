-- Prove2me | Theorems.Thm_NestedCRP_path_conditional_truncated
-- name    : NestedCRP.path_conditional_truncated
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:45.381892+00:00
-- url     : https://prove2.me/theorems/67e06190-c64a-46de-8691-485b04b82127
-- title:
--   Eq. (4) on paths of length $\max(z_d)$
-- statement:
--   Fix level allocations, a document $d$, a tree $T_0$, and a tree $T'$ with the same restriction to the other documents as $T_0$. Let $L=\max(z_d)$. Sum the path weights over the trees that agree with $T_0$ off $d$ and with $T'$ at all levels $\ell\le L$, that is, over the continuations of the path of $d$ below level $L$. The sum converges to
--
--   $$
--   \prod_{\ell<L}\mathrm{seat}\bigl(T',d,\ell,\{e\ne d\}\bigr)\cdot\prod_{\ell\le L}R_\ell(T').
--   $$
--
--   The first product is the prior of the path down to level $L$ and the second is the word likelihood, which is Eq. (4) in the form the page prints.
--
--   Differences from the source:
--   - encoding: a path of length max(z_d), levels 1 to max(z_d) → the nodes of d at the levels ℓ ≤ L = max(z_d) with 0-based levels, given by the partitions at those levels; reason: with the restriction to the others fixed, those partitions determine exactly those nodes
--   - encoding: a vocabulary of V words, nonempty implicitly → [NeZero V], that is V ≥ 1; reason: nondegeneracy only: at V = 0 the symmetric Dirichlet on the empty simplex is undefined and the Γ(Vη) = Γ(0) factors of the path weights are poles; no instance of the source is excluded
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.2, Eq. (4) and second display, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_pathWeight

namespace NestedCRP

/-- Eq. (4) in the truncated form the page prints, "paths of that length": summing the path weights
over all continuations below level `max(z_d)` gives the prior of the path down to that level times
the word likelihood. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, Eq. (4) and second display, p.7:17.

**Formalization Note** With 0-based levels the path of length `max(z_d)` has nodes at the levels
`ℓ ≤ L = max(z_d)`, and its prior is the product of the table choices at the levels `ℓ < L`. -/
theorem path_conditional_truncated {V D : ℕ} [NeZero V] (H : Hyper) (C : Corpus V D) (z : C.Levels)
    (d : Fin D) (T₀ T' : Tree D) (hT' : T₀.AgreesOff d T') :
    let L := Finset.univ.sup (z d)
    HasSum
      (fun T'' : {T'' : Tree D // T₀.AgreesOff d T'' ∧ ∀ ℓ ≤ L, T''.part ℓ = T'.part ℓ} =>
        pathWeight H C z d T''.1)
      ((∏ ℓ ∈ Finset.range L, seat H.gamma T' d ℓ (Finset.univ.erase d)) *
        ∏ ℓ ∈ Finset.range (L + 1), levelRatio H.eta C z T' d ℓ) := by sorry

end NestedCRP
