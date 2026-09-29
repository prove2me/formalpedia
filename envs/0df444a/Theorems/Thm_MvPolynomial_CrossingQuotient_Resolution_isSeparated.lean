-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isSeparated
-- name    : MvPolynomial.CrossingQuotient.Resolution.isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/589246fb-6b3f-586f-99db-c1dd8586c0bd
-- title:
--   Separatedness of the glued resolution of xy = t^e
-- statement:
--   Let $W$ be a commutative ring (in universe $u$), let $t \in W$, and let $e$ be a natural number. Form the scheme `Resolution t e`, defined as the colimit in the category of schemes of the diagram `glueDiagram t e` indexed by the category `GlueIndex e`, whose objects are the schemes `glueObj t e` and whose morphisms are the gluing maps `glueMap t e`; this is the scheme obtained by gluing the charts of the resolution of the crossing $xy = t^e$ over $W$. Form also the affine scheme `crossingScheme (t ^ e)`, namely the spectrum of $W[X_0,X_1]/(X_0X_1 - t^e)$, and the morphism `Resolution.toCrossing t e` from `Resolution t e` to it, obtained from the universal property of the colimit applied to the cocone `crossingCocone t e` on `glueDiagram t e` with vertex `crossingScheme (t ^ e)` and components `crossingCoconeApp t e`. The theorem asserts the conjunction of two facts: the scheme `Resolution t e` is separated in the absolute sense of `Scheme.IsSeparated`, and the morphism `Resolution.toCrossing t e` is a separated morphism of schemes, i.e. its diagonal is a closed immersion.
--
--   This is the separatedness half of the statement that the glued chart model of the resolution of the $A_{e-1}$-type crossing $xy = t^e$ behaves as a scheme over $\operatorname{Spec} W[X_0,X_1]/(X_0X_1-t^e)$ should. It is used in the proof that `Resolution.toCrossing` is proper and in the results producing closed immersions and lifts of morphisms into the resolution, and thence in the comparison of models used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_isSeparated.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.Resolution.isSeparated
    {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    (Resolution t e).IsSeparated ∧ IsSeparated (Resolution.toCrossing t e) := by sorry
