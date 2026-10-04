-- Prove2me | Theorems.Thm_KKBinPacking_GeometricGrouping_lp_floor_rounding_certificate
-- name    : KKBinPacking.GeometricGrouping.lp_floor_rounding_certificate
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-02T13:48:50.565035+00:00
-- url     : https://prove2.me/theorems/d4f0eca3-b658-4ba1-82b1-267d1e0de27c
-- title:
--   Floor-rounding certificate for a feasible configuration LP
-- statement:
--   Let $I$ be a finite bin-packing instance with real item sizes in $(0,1)$, and let $x$ be any nonnegative feasible vector of the configuration LP. For each configuration $c$, take $\lfloor x_c\rfloor$ copies as principal bins. Write
--
--   $$N=\sum_c\lfloor x_c\rfloor,\qquad s=|\operatorname{supp}(x)|.$$
--
--   Let $R$ contain the items left after filling all available principal slots by type, with no original item used more than once. Thus its multiplicity at each size $t$ is
--
--   $$b_t(R)=\max\!\left\{b_t(I)-\sum_c\lfloor x_c\rfloor a_{tc},\,0\right\},$$
--
--   where $a_{tc}$ is the multiplicity of size $t$ in configuration $c$. There is a packing $P$ of the removed items satisfying
--
--   $$|P|\le N,\qquad SIZE(R)\le\sum_c x_c-N,\qquad OPT(R)\le s.$$
--
--   This certificate separates the combinatorial floor-and-delete operation from sparsity and LP optimality. Together with the elementary packing bound on $R$, it supplies the rounding ingredient of Lemma 2.
--
--   **Formalization Note** Multiset subtraction truncates negative counts to zero. Principal configurations may over-cover the input; $P$ contains the retained original items, with excess configuration slots removed. Empty bins are allowed. The certificate covers every feasible $x$, not only basic or optimal solutions.
-- source:
--   Karmarkar and Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, FOCS 1982, p. 313, Lemma 2, proof of the additive upper bound. https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf

import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem lp_floor_rounding_certificate
    (I : Multiset ℝ) (hI : IsInstance I)
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible I x) :
    let R := I - (principalConfigs x).join
    ∃ P : Multiset (Multiset ℝ),
      IsPacking (I - R) P ∧
      P.card ≤ principalCount x ∧
      SIZE R ≤ lpCost x - (principalCount x : ℝ) ∧
      (OPT R : ℝ) ≤ (x.support.card : ℝ) := by sorry
end KKBinPacking.GeometricGrouping
