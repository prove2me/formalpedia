-- Prove2me | Theorems.Thm_MazurReduction_rational_torsion_kernel_zero
-- name    : MazurReduction.rational_torsion_kernel_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T10:34:37.18199+00:00
-- url     : https://prove2.me/theorems/3fde7ecc-617b-4932-84d5-80216f7fafe5
-- title:
--   Full rational torsion has trivial odd good-reduction kernel
-- statement:
--   Let p>2 be a rational prime and W an integral Weierstrass model over the p-adic valuation ring of the rationals. Assume its rational curve is elliptic and its reduced discriminant is nonzero. Every rational torsion point in the kernel of the good-reduction homomorphism is the identity. This covers all finite orders, including those divisible by p. A decidable-equality instance on the residue field is a computational parameter and is always available classically.
-- source:
--   New proof by Vasily Ilin, October 2026. Generic reduction map and prime-to-residue-characteristic integrality: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2. Odd division-polynomial criterion already Proved on Prove2Me: https://prove2.me/theorems/169656be-f5e2-52a1-a76b-54f92944f1b2.

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine

theorem MazurReduction.rational_torsion_kernel_zero
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    [DecidableEq (ResidueField (Rat.padicValuation p).valuationSubring)]
    (W : WeierstrassCurve (Rat.padicValuation p).valuationSubring)
    [(W.map (Rat.padicValuation p).valuationSubring.subtype).IsElliptic]
    (hΔ : (W.map (residue (Rat.padicValuation p).valuationSubring)).Δ ≠ 0)
    (P : (W.map (Rat.padicValuation p).valuationSubring.subtype).toAffine.Point)
    (hP : IsOfFinAddOrder P)
    (hred : WeierstrassCurve.reduceHom hΔ P = 0) : P = 0 := by sorry
