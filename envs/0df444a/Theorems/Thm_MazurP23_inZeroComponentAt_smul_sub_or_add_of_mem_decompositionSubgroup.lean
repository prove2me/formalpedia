-- Prove2me | Theorems.Thm_MazurP23_inZeroComponentAt_smul_sub_or_add_of_mem_decompositionSubgroup
-- name    : MazurP23.inZeroComponentAt_smul_sub_or_add_of_mem_decompositionSubgroup
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:09:45.567792+00:00
-- url     : https://prove2.me/theorems/8a7e6727-cda4-4345-84ef-7520c3e968e8
-- title:
--   Decomposition group moves a torsion point within its component class up to sign
-- statement:
--   Promoted from the Frey proof (helper tw_dich): at a multiplicative prime, a decomposition-group element sends an odd-order torsion point P to a point with sigma P - P or sigma P + P in the identity component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Definitions.Def_EllipticCurve_ZeroComponentAt
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23
theorem inZeroComponentAt_smul_sub_or_add_of_mem_decompositionSubgroup (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσD : σ ∈ A.decompositionSubgroup ℚ)
    {n : ℕ} (hn : Odd n) (hn1 : 1 < n) (hnq : ¬ q ∣ n)
    (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (htor : n • x = 0) (hout : ¬ W.InZeroComponentAt A x) :
    W.InZeroComponentAt A (σ • x - x) ∨ W.InZeroComponentAt A (σ • x + x) := by sorry
end MazurP23
