-- Prove2me | Theorems.Thm_OAI_Problem313_inverse_noise_energy_le
-- name    : OAI.Problem313.inverse_noise_energy_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:37:24.238875+00:00
-- url     : https://prove2.me/theorems/bbe91986-0928-4804-923b-726668e95476
-- title:
--   Undoing noise on low degrees costs $\rho^{-2k}$
-- statement:
--   Let $(c_i)$ be finitely many coefficients with degrees $\deg(i)\in\mathbb{N}$, supported in degrees at most $k$ (i.e. $c_i\ne0\Rightarrow\deg(i)\le k$), and let $0<\rho\le1$. Then
--   $$
--   \sum_i\bigl(\rho^{-\deg(i)}c_i\bigr)^2\le\rho^{-2k}\sum_ic_i^2 .
--   $$
--
--   Inverting the noise operator $T_\rho$ on functions of degree at most $k$ increases the $L^2$ norm by at most $\rho^{-k}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/LowDegreeL4.lean#L13-L33

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities

open OAI OAI.Problem313
universe u v
open scoped BigOperators

theorem OAI.Problem313.inverse_noise_energy_le {ι : Type u} [Fintype ι]
    (degree : ι → ℕ) (c : ι → ℝ) (rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ i, (rho ^ (-(degree i : ℝ)) * c i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 := by sorry
