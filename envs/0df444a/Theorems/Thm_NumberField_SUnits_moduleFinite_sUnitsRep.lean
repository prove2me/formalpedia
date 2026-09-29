-- Prove2me | Theorems.Thm_NumberField_SUnits_moduleFinite_sUnitsRep
-- name    : NumberField.SUnits.moduleFinite_sUnitsRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/484e3c01-fd4b-5ddd-9300-2e1c7fda1e3b
-- title:
--   Finite generation of the S-unit Galois representation
-- statement:
--   Let $E$ and $K$ be number fields (fields of characteristic zero, finite over $\mathbb{Q}$, with $K$ an $E$-algebra), and let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_E$, i.e. a `Finset (HeightOneSpectrum (𝓞 E))`. Consider the $\mathbb{Z}$-submodule `sUnitsSubmodule E K S` of $\mathrm{Additive}\,K^{\times}$ obtained from the subgroup `sUnits E K S` of $K^{\times}$ by passing to its additive form, and the representation `sUnitsRep E K S` of the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$ on this submodule: it is the subrepresentation of the representation of $\mathrm{Aut}_E(K)$ on $\mathrm{Additive}\,K^{\times}$ coming from the multiplicative action on units, the submodule being stable under the action by `smul_mem_sUnits`. The assertion is that this object of $\mathrm{Rep}\ \mathbb{Z}\ (K \simeq_{\mathrm{alg}[E]} K)$ is finite as a $\mathbb{Z}$-module, that is, its underlying abelian group `sUnitsSubmodule E K S` is finitely generated. No statement is made about its rank, nor about the Galois action beyond its existence.
--
--   This is the module-theoretic form of the Dirichlet–Chevalley–Hasse $S$-unit theorem: the group of $S$-units of $K$, regarded as a $\mathrm{Gal}(K/E)$-module, is a finitely generated abelian group. It serves as the finiteness input for cohomological computations with the $S$-unit representation, and is used in the construction of level data for maps out of $S$-unit cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_moduleFinite_sUnitsRep.lean

import Mathlib
import Definitions.Def_NumberField_SUnitsModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem NumberField.SUnits.moduleFinite_sUnitsRep (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) : Module.Finite ℤ (NumberField.SUnits.sUnitsRep E K S) := by sorry
