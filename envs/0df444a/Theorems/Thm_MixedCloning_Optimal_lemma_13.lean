-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_13
-- name    : MixedCloning.Optimal.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:04:53.715281+00:00
-- url     : https://prove2.me/theorems/72f75d16-6e43-4f4c-b5ea-d14022963be6
-- title:
--   Lemma 13 — permutation symmetrization preserves overlap
-- statement:
--   Let $1\le r\le d$ and $n,m\ge0$. For every channel $C$ from $n$ to $m$ copies of $\mathbb C^d$, there is a channel $\overline C$ invariant under independent input and output register permutations. For every rank-$r$ orthogonal projector $P$, setting $\rho=P/r$, one has
--
--   $$\operatorname{tr}(\overline C(\rho^{\otimes n})P^{\otimes m})=\operatorname{tr}(C(\rho^{\otimes n})P^{\otimes m}).$$
--
--   The minimum overlap over all these projectors and the Haar-average overlap are equal for $C$ and $\overline C$. Invariance is required on every operator, including non-product inputs. This justifies restricting the lower-bound analysis to permutation-invariant channels.
--
--   Differences from the source:
--   - generalization: the section uses m=n+k → arbitrary n,m ≥ 0; reason: the displayed symmetrization identity holds for every pair of tensor powers, including zero copies
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 17, Lemma 13

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_13 (d r n m : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (C : Cloner d n m) (hC : QAlgorithms.IsChannel C) :
    ∃ Cbar : Cloner d n m, QAlgorithms.IsChannel Cbar ∧ PermInvariant d n m Cbar ∧
      (∀ P : Op (Fin d), IsProjector r P → overlap d r n m Cbar P = overlap d r n m C P) ∧
      minimumOverlap d r n m Cbar = minimumOverlap d r n m C ∧
      averageOverlap d r n m Cbar = averageOverlap d r n m C := by sorry

end MixedCloning.Optimal
