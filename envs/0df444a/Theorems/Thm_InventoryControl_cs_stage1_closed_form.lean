-- Prove2me | Theorems.Thm_InventoryControl_cs_stage1_closed_form
-- name    : InventoryControl.cs_stage1_closed_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:18:03.293061+00:00
-- url     : https://prove2.me/theorems/2d7fc6db-4044-46f9-aec5-8be6c9b00a9f
-- title:
--   Eq. (10.6): $\hat C_1(\hat y_1) = e_1\hat y_1 - h_1\mu_1'' + (h_1+b_1)\sigma_1''\,G\!\left(\frac{\hat y_1 - \mu_1''}{\sigma_1''}\right)$
-- statement:
--   The stage-1 cost as a function of a freely chosen realized position $\hat y_1$ has the closed
--   form
--
--   $$ \hat C_1(\hat y_1) \;=\; e_1\hat y_1 - h_1\mu_1'' + (h_1 + b_1)\,\sigma_1''\,G\!\left(\frac{\hat y_1 - \mu_1''}{\sigma_1''}\right), $$
--
--   where $\mu_1'' = (L_1+1)\mu$, $\sigma_1'' = \sqrt{L_1+1}\,\sigma > 0$, $h_1 = e_1 + e_2$, and
--   $G$ is the standard normal loss function of Eq. (5.40).
--
--   The book obtains it by writing the expected backorders $\mathbb{E}(\hat y_1 - D(L_1+1))^{-}$
--   as an integral of the normal density and substituting $v = (u - \mu_1'')/\sigma_1''$. It is the
--   same computation as Eq. (5.89) for the newsboy model, and the book says so: "the optimization
--   of (10.6) is essentially a newsboy problem".
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 195, Sect. 10.1.1, Eq. (10.6)

import Definitions.Def_InventoryControl_clarkScarf

namespace InventoryControl

theorem cs_stage1_closed_form (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 : ℕ) (y : ℝ) :
    csStage1Cost e1 e2 b1 mu sigma L1 y
      = e1 * y - (e1 + e2) * ((L1 + 1) * mu)
        + (e1 + e2 + b1) * (Real.sqrt (L1 + 1) * sigma)
            * normalLoss ((y - (L1 + 1) * mu) / (Real.sqrt (L1 + 1) * sigma)) := by sorry

end InventoryControl
