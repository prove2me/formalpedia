-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_LocalDVR_dvd_or_dvd_of_mul_eq_pow_mul_unit
-- name    : OAI.CirculantHadamard.LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:17:38.679291+00:00
-- url     : https://prove2.me/theorems/16986ffd-da95-4482-a4c6-85d222320300
-- title:
--   A product equal to a high prime power times a unit
-- statement:
--   Let $R$ be a discrete valuation ring with additive valuation $v$, and let $p\ne0$ with $v(p)=D>0$. If $e\ge2$, $b$ is a unit and
--   $$
--   xy=p^e\,b,
--   $$
--   then $p\mid x$ or $p\mid y$.
--
--   The valuation $eD\ge2D$ of the product must give at least $D$ to one of the two factors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/LocalDVR.lean#L82-L104

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalDVR
universe uR
open IsLocalRing IsDiscreteValuationRing
variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem OAI.CirculantHadamard.LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit {p x y b : R} {D e : ℕ}
    (_hp : p ≠ 0) (_hD : 0 < D) (hpval : addVal R p = (D : ℕ∞))
    (he : 2 ≤ e) (hb : IsUnit b) (hxy : x * y = p ^ e * b) :
    p ∣ x ∨ p ∣ y := by sorry
