-- Prove2me | Theorems.Thm_Ideal_finrank_residueField_eq_inertiaDegIn_of_heightOne
-- name    : Ideal.finrank_residueField_eq_inertiaDegIn_of_heightOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:06:14.120559+00:00
-- url     : https://prove2.me/theorems/cc2ef81d-060d-4612-9f26-a04cb4e019dc
-- title:
--   Ideal: finrank residue Field eq inertia Deg In of height One
-- statement:
--   A height-one prime whose valuation agrees with a normalized discrete
--   valuation gives the same residue-field finrank as the common Galois inertia
--   degree.  This packages the quotient/residue transport away from concrete
--   function-field towers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ResidueFinrankInertia.lean#L93-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ResidueFinrankInertia.lean#L93-L119

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ResidueFinrankInertia
set_option autoImplicit false
open Ideal
noncomputable section

theorem Ideal.finrank_residueField_eq_inertiaDegIn_of_heightOne
    {k O C K G : Type*} [Field k] [Finite k]
    [CommRing O] [IsDedekindDomain O] [CommRing C] [IsDedekindDomain C]
    [Algebra O C] [Module.Finite O C]
    [Field K] [Algebra C K] [IsFractionRing C K]
    [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G O C]
    (p : Ideal O) [p.IsMaximal]
    (H : IsDedekindDomain.HeightOneSpectrum C)
    (hH : H.asIdeal.LiesOver p)
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [Algebra k (IsLocalRing.ResidueField v.valuationSubring)]
    [FiniteDimensional k (IsLocalRing.ResidueField v.valuationSubring)]
    (baseEquiv : k ≃+* (O ⧸ p)) (hv : H.valuation K = v) :
    Module.finrank k (IsLocalRing.ResidueField v.valuationSubring) =
      p.inertiaDegIn C := by sorry
