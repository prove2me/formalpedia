-- Prove2me | Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
-- name    : ModularCurve.essFiniteType_modularFunctionFieldFullC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/93f76987-ade0-5c09-ae28-ad02fe503552
-- title:
--   Full-level modular function field is essentially of finite type
-- statement:
--   Let $K$ be a field and let $N$ be a natural number with $N \neq 0$. Inside the field of Laurent series $\mathrm{LaurentSeries}\,K$ consider the set `divisorExpansionsC K N` consisting of those series of the form `qExpand K d (jqModC K)` for some nonzero natural number $d$ dividing $N$, i.e. the $d$-fold $q$-substitutions of the single series `jqModC K`, and let `modularFunctionFieldFullC K N` be the intermediate field $K \subseteq \cdot \subseteq \mathrm{LaurentSeries}\,K$ obtained by adjoining this set to $K$. The theorem asserts that this intermediate field, regarded as a $K$-algebra via its coercion to a type, satisfies `Algebra.EssFiniteType K`, that is, it is essentially of finite type over $K$ (a localisation of a finite-type $K$-subalgebra); for a field extension this amounts to being finitely generated as a field extension of $K$. No hypothesis is imposed on the characteristic of $K$ or on its relation to $N$.
--
--   This records the finiteness needed to treat the full-level-$N$ modular function field over an arbitrary base field as the function field of a curve over $K$; the proof combines the transcendence of the chosen generator with finiteness of the extension it generates, using the existence of modular polynomial data for level $N$. It underlies the Riemann–Roch and canonical-divisor machinery for this field, and is invoked throughout the `ModularCurve.FullLevel` development, for instance in the construction of cusp-regular separating elements and in the comparison of Riemann–Roch spaces with residues at places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.essFiniteType_modularFunctionFieldFullC (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Algebra.EssFiniteType K ↥(ModularCurve.modularFunctionFieldFullC K N) := by sorry
