-- Prove2me | Theorems.Thm_GreenTao_cs_endpoint_identities
-- name    : GreenTao.cs_endpoint_identities
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:34:59.462785+00:00
-- url     : https://prove2.me/theorems/8ca08e1d-fd9b-482d-b13e-6010cf1c50c4
-- title:
--   Endpoint reparameterizations of the progression CS stages
-- statement:
--   Let $d\ge2$, let $m>d$ be prime, let $\mu\ge0$ be a real majorant on $\mathbb Z/m\mathbb Z$, and let $F_0,\ldots,F_d$ be arbitrary real functions. For each distinguished position $j$, the explicit Cauchy–Schwarz stages satisfy
--
--   $$J_0=T_{d+1}(F_0,\ldots,F_d),\qquad J_d=C_d^W(F_j).$$
--
--   The first identity reparameterizes ordered progressions by the coordinate forms $\phi_i$. The second changes the fully duplicated coordinate vectors into a Gowers cube and the explicit cube weight. Both statistics use uniform averages and include zero common differences. This isolates the finite endpoint changes of variables from the Cauchy–Schwarz inequalities and the asymptotic moment calculations.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 equations (5.22), (5.23), and (5.25), including the uniform-cover argument and the paired expression for the cube weight. The weight is expressed in the project’s progression-difference coordinates.

import Definitions.Def_GreenTao_ProgressionCS

theorem GreenTao.cs_endpoint_identities
    (d : ℕ) (hd : 2 ≤ d) (m : ℕ+) (hm : Nat.Prime (m : ℕ)) (hdm : d < (m : ℕ))
    (μ : ZMod (m : ℕ) → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (j : Fin (d + 1)) (F : Fin (d + 1) → ZMod (m : ℕ) → ℝ) :
    GreenTao.csStage d j μ F 0 = GreenTao.mixedAPAvg (d + 1) F ∧
      GreenTao.csStage d j μ F d =
        GreenTao.weightedCubeAvg d (GreenTao.csWeight d j μ) (F j) := by sorry
