-- Prove2me | Theorems.Thm_NestedCRP_level_prior
-- name    : NestedCRP.level_prior
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:23.17456+00:00
-- url     : https://prove2.me/theorems/d3919f39-fa16-4bc4-b7d6-6a1299f472b2
-- title:
--   Level prior $p(z_{d,n}=k\mid z_{d,-n},m,\pi)$
-- statement:
--   Let $\zeta$ be a vector of levels of the words of a document, and $n$ a word. For every level $k$,
--
--   $$
--   \mathrm{stick}(\zeta[n\mapsto k])=\frac{m\pi+\#[z'=k]}{\pi+\#[z'\ge k]}\prod_{j<k}\frac{(1-m)\pi+\#[z'>j]}{\pi+\#[z'\ge j]}\;\mathrm{stick}(z'),
--   $$
--
--   where $z'$ leaves out word $n$. The factors sum to one over $k\in\mathbb N$.
--
--   So the display of §5.1 is the conditional law of a word's level given the other levels of the document, with the sticks integrated out, and it is a distribution on all levels.
--
--   Differences from the source:
--   - generalization: the display is printed for k ≤ max(z_{d,-n}) → the identity holds for every level k; reason: the source's derivation covers all k; the printed range is a special case
--   - generalization: the words of one document, indexed by 1..N_d → any finite index type for the words; reason: it specializes to Fin (N d)
--   - encoding: the conditional p(z_{d,n} = k | z_{d,-n}, m, π) → the ratio of marginal masses, cross-multiplied; reason: the definition of a conditional; the marginals are positive
--   - encoding: levels and sticks are 1-based → levels and sticks are 0-based; reason: Lean indexing; level ℓ here is the paper's level ℓ + 1, and no instance changes
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.1, third display, p.7:16

import Mathlib
import Definitions.Def_NestedCRP_Hyper
import Definitions.Def_NestedCRP_stickMass

namespace NestedCRP

/-- The level prior of §5.1 is a law on all levels, and it is the ratio of the marginal level masses
with and without word `n`: `p(z_{d,n} = k | z_{d,-n}, m, π)`.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.1, third display, p.7:16.

**Formalization Note** The identity is stated at every `k`, not only at `k ≤ max(z_{d,-n})`. -/
theorem level_prior (H : Hyper) {ι : Type*} [Fintype ι] [DecidableEq ι] (ζ : ι → ℕ) (n : ι) :
    (∀ k, stickMass H.m H.pi (Function.update ζ n k) =
      levelPrior H.m H.pi ζ n k * stickMass H.m H.pi (fun i : {i // i ≠ n} => ζ i)) ∧
    HasSum (levelPrior H.m H.pi ζ n) 1 := by sorry

end NestedCRP
