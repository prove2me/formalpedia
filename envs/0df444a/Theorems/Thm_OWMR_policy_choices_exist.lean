-- Prove2me | Theorems.Thm_OWMR_policy_choices_exist
-- name    : OWMR.policy_choices_exist
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T19:38:23.854535+00:00
-- url     : https://prove2.me/theorems/27a24d7a-430b-49d0-b583-30ac57a43997
-- title:
--   The choices required by Definitions 1, 2 and D.1 exist, so Theorems 1, 2 and D.1 are not vacuous
-- statement:
--   Definitions 1, 2 and D.1 of the source leave several choices open: optimal retailer and supplier $(s,S)$ pairs satisfying the canonical conditions, half windows with the smallest holding and backlog cost, minimizers, mirror centers, the shortened windows and targets of the DFR policy, and the initialization data of the consolidation policy. Theorems 1, 2 and D.1 hold for every admissible choice. This theorem shows that admissible choices always exist, so the three guarantees are not vacuous.
--
--   Let $N$ be a one-warehouse multi-retailer network with $n\ge1$ retailers under the standing assumptions of Section 3: demand vectors are i.i.d. over periods with $0<\mathbb E D_i<\infty$ for every retailer, $K_0,K_i\ge0$, and $h,H_i,p>0$. Then:
--
--   1. **Definition 1.** There are choices $c=(s_i,S_i,a_i,s_0,S_0)$ satisfying `IsFIFOChoice N c`: for each retailer with $K_i>0$, a canonical optimum $(\hat s_i,\hat S_i)$ at planning setup cost $5K_i/3$, a best half window of $[\hat s_i,\hat S_i]$, whichever of the two has the smaller augmented cost, and a mirror center of the selected policy; base stock at a minimizer of $F_i$ when $K_i=0$; and a supplier pair $s_0\le S_0$ whose average cost equals $J_0(K_0+K_{\max})$.
--   2. **Definition 2.** For every $m>0$ there are choices satisfying `IsConChoice N m c`: immediate retailers using base stock at a minimizer of $F_i$, batch retailers using a canonical optimum at setup cost $\zeta_mK_i$ or its best half window according to the setup share, the shifted supplier pair (or, if $K_0=0$, base stock at a nonnegative minimizer of $f_{L_0}$), a retailer receiving the initial warehouse stock, initial offsets in $(0,1)$, and an enumeration of the rationals in $(0,1)$.
--   3. **Definition D.1.** For every $\theta>0$, if every retailer with $K_i>0$ has an absolutely continuous DFR demand distribution conditional on positive demand (`DFRPositive`), there are choices satisfying `IsDFRChoice N θ c`: in particular, whenever $t_0<t<1$, a width $w>0$ with $U[0,w)=t\,U[0,\hat w)$, a target minimizing the average holding and backlog cost among width-$w$ policies, and a mirror center.
--
--   Theorem 2 uses $m\ge1$ and Theorem D.1 uses $\theta=1-1/\gamma_\lambda$, both covered here, and the cost conditions of Theorems 1, 2 and D.1 are not needed for existence.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 3, Definition 1 (FIFO Policy), p. 9; Section 6, Definition 2 (Consolidation Policy) with the constants (33), p. 28; Appendix D, Definition D.1 (DFR Policy) and the demand assumption of Theorem D.1, p. E.23; existence of canonical optimal pairs from Lemma 1, p. 12, and the remark before it ("Coercivity ensures an optimal policy with finite reorder and order-up-to levels").

import Definitions.Def_owmr_fifo_policy
import Definitions.Def_owmr_consolidation_policy
import Definitions.Def_owmr_dfr_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem policy_choices_exist {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) :
    (∃ c : FIFOChoice n, IsFIFOChoice N c) ∧
    (∀ m : ℝ, 0 < m → ∃ c : ConChoice n, IsConChoice N m c) ∧
    (∀ θ : ℝ, 0 < θ → (∀ i, 0 < N.K i → N.DFRPositive i) →
      ∃ c : FIFOChoice n, IsDFRChoice N θ c) := by sorry
end OWMR
