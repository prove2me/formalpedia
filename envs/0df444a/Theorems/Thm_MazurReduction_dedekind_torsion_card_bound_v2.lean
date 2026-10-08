-- Prove2me | Theorems.Thm_MazurReduction_dedekind_torsion_card_bound_v2
-- name    : MazurReduction.dedekind_torsion_card_bound_v2
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T11:59:49.41834+00:00
-- url     : https://prove2.me/theorems/8973b133-a43c-4840-bc8d-18e78d1b8ac1
-- title:
--   Full torsion bound at an unramified odd Dedekind prime
-- statement:
--   For an integral Weierstrass model over a Dedekind domain R with fraction field K, good reduction at a height-one prime v with finite residue field bounds the entire K-rational torsion group: it is finite and its cardinality divides that of the special fibre, provided v(p)=exp(-1) for an odd rational prime p. All torsion orders, including multiples of p, are covered. Named downstream consumer: the order-18 elliptic quotient over the real cubic coefficient field, whose chosen unramified prime above 17 has a 21-point special fibre.
-- source:
--   Vasily Ilin, October 2026. Generic reduction/integrality and division criterion reused from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2. Residue-map infrastructure: Michael Stoll, Apache-2.0, MichaelStollBayreuth/EllipticCurves at 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f, as integrated in the user MazurTheorem WIP. All original source headers retained in the submitted proof.

import Mathlib
import Definitions.Def_MazurReduction_DedekindResidueTypes
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open scoped WeierstrassCurve.Affine

theorem MazurReduction.dedekind_torsion_card_bound_v2
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hv : v.valuation K (p : K) = exp (-1 : ℤ))
    (W : WeierstrassCurve R) [(W.map (algebraMap R K)).IsElliptic]
    [(W.map (algebraMap R (R ⧸ v.asIdeal))).IsElliptic] :
    Finite (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point) ∧
      Nat.card (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point) ∣
        Nat.card (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point := by sorry
