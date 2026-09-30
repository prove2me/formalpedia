-- Prove2me | Theorems.Thm_InventoryControl_cs_stage1_optimal
-- name    : InventoryControl.cs_stage1_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:18:35.296986+00:00
-- url     : https://prove2.me/theorems/f4a80d75-f112-47d7-829f-b53dd0d6b225
-- title:
--   Eq. (10.7)-(10.8): $\hat C_1$ is convex and $\hat y_1$ is optimal iff $\Phi\!\left(\frac{\hat y_1 - \mu_1''}{\sigma_1''}\right) = \frac{e_2 + b_1}{h_1 + b_1}$
-- statement:
--   With echelon holding costs $e_1, e_2 \ge 0$, shortage cost $b_1 > 0$ and $\sigma > 0$, the
--   stage-1 cost $\hat C_1$ of Eq. (10.6) is a convex function of $\hat y_1$ on $\mathbb{R}$, it is
--   differentiable with
--
--   $$ \frac{\mathrm{d}\hat C_1(\hat y_1)}{\mathrm{d}\hat y_1} \;=\; e_1 + (h_1 + b_1)\left(\Phi\!\left(\frac{\hat y_1 - \mu_1''}{\sigma_1''}\right) - 1\right), $$
--
--   and a level $\hat y_1$ minimizes $\hat C_1$ over $\mathbb{R}$ if and only if
--
--   $$ \Phi\!\left(\frac{\hat y_1 - \mu_1''}{\sigma_1''}\right) \;=\; \frac{e_2 + b_1}{h_1 + b_1}, $$
--
--   where $h_1 = e_1 + e_2$, $\mu_1'' = (L_1+1)\mu$ and $\sigma_1'' = \sqrt{L_1+1}\,\sigma$.
--
--   Convexity comes from that of the loss function $G$ (Eq. 5.41), and the derivative from
--   $G' = \Phi - 1$. The fractile is a newsboy critical fractile with overage cost $e_1$ and
--   underage cost $e_2 + b_1$: a unit held at installation 1 rather than at installation 2 costs
--   the value added $e_1$, and a unit short costs $b_1$ plus the holding cost $e_2$ it would have
--   incurred anyway. When $e_1 = 0$ the fractile is $1$, no finite minimizer exists, and the book
--   notes that installation 2 then never carries stock.
--
--   **Formalization Note** The fractile condition is stated as the characterization of the
--   minimizers; existence and uniqueness of the solution for $e_1 > 0$ follow from the
--   strict monotonicity of $\Phi$ as in the newsboy mission.
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 195, Sect. 10.1.1, Eq. (10.7) and Eq. (10.8): 'it is easy to get the optimal y-hat1 from the first order condition ... or equivalently Phi((y-hat1 - mu''1)/sigma''1) = (e2 + b1)/(h1 + b1)'

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem cs_stage1_optimal (e1 e2 b1 mu sigma : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hb : 0 < b1)
    (hs : 0 < sigma) (L1 : ℕ) (S1 : ℝ) :
    ConvexOn ℝ Set.univ (csStage1Cost e1 e2 b1 mu sigma L1)
      ∧ HasDerivAt (csStage1Cost e1 e2 b1 mu sigma L1)
          (e1 + (e1 + e2 + b1)
            * (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
                ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) - 1)) S1
      ∧ ((∀ y : ℝ, csStage1Cost e1 e2 b1 mu sigma L1 S1 ≤ csStage1Cost e1 e2 b1 mu sigma L1 y)
          ↔ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
              ((S1 - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma))
              = (e2 + b1) / (e1 + e2 + b1)) := by sorry

end InventoryControl
