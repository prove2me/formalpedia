-- Prove2me | Theorems.Thm_G2GImport_Sourcing_ad_hoc_stage
-- name    : G2GImport.Sourcing.ad_hoc_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:39.440994+00:00
-- url     : https://prove2.me/theorems/b3a3801b-fb68-4674-a68f-0b2f4bc0686b
-- title:
--   Equation (A.2): ad hoc purchase and payment, general and symmetric
-- statement:
--   Fix a realized yield $y\in[0,1]$, a nonnegative production quantity $k$ of the focal ad hoc supplier and buyer bargaining power $\gamma\in(0,1)$; there are no forward suppliers. Write $u(x)=2x-x^2$. Let $O\ge0$ be the total quantity the other ad hoc suppliers have agreed to sell, held fixed (Nash-in-Nash). The focal pair $(q,t)$ is a Nash bargaining solution exactly when
--   $$q=\max\{0,\min\{k,1-y-O\}\},\qquad t=(1-\gamma)\bigl[u(\min\{1,y+O+q\})-u(\min\{1,y+O\})\bigr].$$
--   In particular, with $l\ge1$ identical ad hoc suppliers whose other $l-1$ agreements equal the same purchase $q$ (so $O=(l-1)q$), the focal pair is a solution exactly when
--   $$q=\min\!\left\{k,\frac{1-y}{l}\right\},\qquad t=(1-\gamma)\bigl[u(\min\{1,y+lq\})-u(\min\{1,y+(l-1)q\})\bigr].$$
--   This stage outcome identifies each supplier's purchase and its share of the incremental buyer utility, providing the quantity rule used in the production stage.
--
--   **Formalization Note** The first part is (A.2) with $Q^f=0$. The feasible purchase is capped by remaining demand. This is the selection expressed in (A.2); it resolves the flat Nash-product region after demand is met.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 8, §4.1 ad hoc outcome; PDF p. 13, equation (A.2)

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model

namespace G2GImport.Sourcing

/-- Equation (A.2) with no forward suppliers: for any total `O ≥ 0` agreed by the other
ad hoc suppliers, the focal bargain buys `max 0 (min k (1 - y - O))` and pays `1 - γ` times
the buyer's marginal utility; in the symmetric case `O = (l - 1) q` this is
`q = min k ((1 - y) / l)`. -/
theorem ad_hoc_stage (γ k y : ℝ) (hγ : 0 < γ ∧ γ < 1) (hk : 0 ≤ k)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (∀ O q t : ℝ, 0 ≤ O →
      (AdHocBargain γ k O y q t ↔
        q = max 0 (min k (1 - y - O)) ∧
        t = (1 - γ) * (supplyUtil (y + O + q) - supplyUtil (y + O)))) ∧
    (∀ (l : ℕ) (q t : ℝ), 1 ≤ l →
      (AdHocBargain γ k (((l : ℝ) - 1) * q) y q t ↔
        q = min k ((1 - y) / (l : ℝ)) ∧
        t = (1 - γ) *
          (supplyUtil (y + (l : ℝ) * q) -
            supplyUtil (y + ((l : ℝ) - 1) * q)))) := by sorry

end G2GImport.Sourcing
