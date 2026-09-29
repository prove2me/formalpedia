-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one
-- name    : Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/49467081-0ed4-54a0-a012-54878453900a
-- title:
--   Unimodularity of GL₂(F): the modular character is trivial
-- statement:
--   Let $F$ be a field carrying a topology making it a topological ring, and suppose that the group $\mathrm{GL}_2(F)$ of units of the ring of $2 \times 2$ matrices over $F$, with its induced topology, is a locally compact space. Let $g$ be an element of $\mathrm{GL}_2(F)$. Then the value at $g$ of the modular character of $\mathrm{GL}_2(F)$ — the homomorphism into the multiplicative monoid of non-negative reals which records, for a left Haar measure $\mu$ on the group, the scalar by which $\mu$ is multiplied when it is translated on the right by $g$, a scalar independent of the choice of $\mu$ — equals $1$. Equivalently, $\mathrm{GL}_2(F)$ is unimodular. No hypothesis beyond the topological ring structure on $F$ and local compactness of $\mathrm{GL}_2(F)$ is imposed: in particular $F$ is not assumed local, nor complete, nor of any particular characteristic, and $2$ may vanish in $F$.
--
--   This is the unimodularity of the general linear group in rank two, in the form that the modular character is identically trivial. It is the input to the statements that a left Haar measure on $\mathrm{GL}_2(F)$ is also right invariant, and invariant under inversion, which is what licenses the unqualified use of "Haar measure" on $\mathrm{GL}_2$ of a local field in the local theory of automorphic representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] (g : GL (Fin 2) F) :
    MeasureTheory.Measure.modularCharacter g = 1 := by sorry
