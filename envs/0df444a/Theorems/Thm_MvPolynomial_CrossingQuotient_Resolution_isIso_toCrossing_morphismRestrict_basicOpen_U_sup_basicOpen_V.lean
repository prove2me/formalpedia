-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V
-- name    : MvPolynomial.CrossingQuotient.Resolution.isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/4fe8f234-6923-5b28-9f85-dea46e38cc95
-- title:
--   Crossing resolution is an isomorphism over D(u)∪ D(v)
-- statement:
--   Let $W$ be a commutative ring, $t\in W$ and $e$ a natural number with $0<e$. Write $\mathrm{CrossingQuotient}\,W\,s=W[X_0,X_1]/(X_0X_1-C(s))$ for $s\in W$, let `crossingScheme s` be its spectrum, and let `Resolution t e` be the colimit of the diagram `glueDiagram t e` indexed by `GlueIndex e`, whose objects are the charts `glueObj t e` and whose maps are the gluing maps `glueMap t e`; `toCrossing t e` is the induced morphism from this colimit to `crossingScheme (t ^ e)` determined by the cocone `crossingCocone t e`, and `Resolution.ι t e i` denotes the structure morphism of the chart with index $i$. Here `U s` and `V s` are the two distinguished elements of `CrossingQuotient W s`. The assertion is a conjunction of five statements: the open image under the structure morphism of the chart indexed by $0$ of the basic open set of `U t` equals the `toCrossing t e`-preimage of the basic open set of `U (t ^ e)`; the open image under the structure morphism of the chart indexed by $e-1$ of the basic open set of `V t` equals the preimage of the basic open set of `V (t ^ e)`; and the restrictions of `toCrossing t e` over the basic open set of `U (t ^ e)`, over the basic open set of `V (t ^ e)`, and over the join of these two opens are isomorphisms of schemes.
--
--   This records that the chart-by-chart resolution of the crossing $uv=t^e$ modifies $\operatorname{Spec} W[u,v]/(uv-t^e)$ only over the locus $u=v=t=0$: over the union of the two coordinate basic opens it is an isomorphism, the first chart and the last chart accounting respectively for $\{u\neq0\}$ and $\{v\neq0\}$. It is used in the construction of resolved Deligne–Rapoport model packages and charts for modular curves, and in the verification of invertibility of the resulting composites.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.Resolution.isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V
    {W : Type u} [CommRing W] (t : W) {e : ℕ} (he : 0 < e) :
    Resolution.ι t e ⟨0, he⟩ ''ᵁ PrimeSpectrum.basicOpen (U t) =
        Resolution.toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen (U (t ^ e)) ∧
      Resolution.ι t e ⟨e - 1, Nat.sub_lt he Nat.one_pos⟩ ''ᵁ PrimeSpectrum.basicOpen (V t) =
        Resolution.toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen (V (t ^ e)) ∧
      IsIso (Resolution.toCrossing t e ∣_ PrimeSpectrum.basicOpen (U (t ^ e))) ∧
      IsIso (Resolution.toCrossing t e ∣_ PrimeSpectrum.basicOpen (V (t ^ e))) ∧
      IsIso (Resolution.toCrossing t e ∣_
        (PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)))) := by sorry
