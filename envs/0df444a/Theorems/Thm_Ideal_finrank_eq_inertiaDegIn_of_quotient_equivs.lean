-- Prove2me | Theorems.Thm_Ideal_finrank_eq_inertiaDegIn_of_quotient_equivs
-- name    : Ideal.finrank_eq_inertiaDegIn_of_quotient_equivs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:51.515922+00:00
-- url     : https://prove2.me/theorems/d88b26d7-a4a5-461e-9764-dd46379418a5
-- title:
--   Ideal: finrank eq inertia Deg In of quotient equivs
-- statement:
--   Ring equivalences from the constant field to the base quotient and from
--   the upper quotient to a finite residue field identify that residue field's
--   dimension with the common Galois inertia degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ResidueFinrankInertia.lean#L21-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/ResidueFinrankInertia.lean#L21-L87

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ResidueFinrankInertia
set_option autoImplicit false
open Ideal
noncomputable section

theorem Ideal.finrank_eq_inertiaDegIn_of_quotient_equivs
    {k O C S G : Type*} [Field k] [Finite k]
    [CommRing O] [IsDedekindDomain O] [CommRing C] [IsDedekindDomain C]
    [Algebra O C] [Module.Finite O C]
    [Field S] [Algebra k S] [FiniteDimensional k S]
    [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G O C]
    (p : Ideal O) [p.IsMaximal] (P : p.primesOver C) [P.1.IsMaximal]
    (baseEquiv : k ≃+* (O ⧸ p))
    (upperEquiv : (C ⧸ P.1) ≃+* S) :
    Module.finrank k S = p.inertiaDegIn C := by sorry
