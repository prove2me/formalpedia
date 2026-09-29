-- Prove2me | Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
-- name    : NumberField.SUnits.sUnits_eq_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c1f43e30-8f8d-5170-bf62-8e5df4c742bd
-- title:
--   Galois-invariant S-units are all S-units
-- statement:
--   Let $E$ be a field and $K$ a number field with an $E$-algebra structure, and let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_E$ (no number-field hypothesis on $E$ is imposed). Write $\mathrm{placesAbove}$ for the set of height-one primes $w$ of $\mathcal{O}_K$ whose contraction $w.\mathrm{under}\,(\mathcal{O}_E)$ along $\mathcal{O}_E \to \mathcal{O}_K$ lies in $S$, and let $\mathrm{Set.unit}$ denote Mathlib's subgroup of $K^\times$ attached to a set of height-one primes of $\mathcal{O}_K$, consisting of the units whose valuation is trivial at every height-one prime outside that set. The project's group [`NumberField.SUnits.sUnits E K S`](def/NumberField_SUnitsModule.html#L25) is defined as the infimum, over all $E$-algebra automorphisms $\sigma$ of $K$, of the pullbacks of $\mathrm{Set.unit}(\mathrm{placesAbove}\,E\,K\,S)$ along the induced map $K^\times \to K^\times$. The theorem asserts that this intersection of all Galois translates equals the single subgroup $\mathrm{Set.unit}(\mathrm{placesAbove}\,E\,K\,S)$ of $K^\times$: imposing the $S$-unit condition on all conjugates $\sigma x$ simultaneously is no stronger than imposing it on $x$ alone.
--
--   This identifies the Galois-stably cut out subgroup used in the project's definition of the $S$-unit group of $K/E$ with the usual group of $S$-units of $K$, namely the units of $K$ integral and invertible outside the primes above $S$. It is the arithmetic input deliberately kept out of the definition itself, and it is used by the downstream idelic and level-arithmetic constructions (capitulation of $S$-unit cocycles, realisation of the $S$-idele class group, and the level computations) to replace the conjugation-stable description by the concrete one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_sUnits_eq_unit.lean

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.SUnits.sUnits_eq_unit (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) :
    NumberField.SUnits.sUnits E K S = Set.unit (NumberField.SUnits.placesAbove E K S) K := by sorry
