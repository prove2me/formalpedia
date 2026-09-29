-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id
-- name    : MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/7e76a970-bb43-5310-bdd2-4143400fad71
-- title:
--   Sections of the resolution of uv=varpi^e meeting one exceptional line
-- statement:
--   Let $O$ be a discrete valuation domain, $\varpi \in O$ and $e \in \mathbb{N}$, and let `Resolution ϖ e` be the scheme obtained as the colimit of the gluing diagram of charts $\operatorname{Spec}$ of `CrossingQuotient O ϖ` $= O[X_0,X_1]/(X_0X_1-\varpi)$, with chart inclusions `ι ϖ e i` for $i \in \mathrm{Fin}\,e$ and structure morphism `Resolution.toSpec ϖ e` to $\operatorname{Spec} O$, namely `Resolution.toCrossing ϖ e` followed by $\operatorname{Spec}$ of the structure map $O \to$ `CrossingQuotient O (ϖ ^ e)`. Let $F : \mathrm{Fin}(e+1) \to$ `(Resolution ϖ e).IdealSheafData` be a family of ideal sheaves satisfying the chart table: for every $i \in \mathrm{Fin}\,e$ and $k \in \mathrm{Fin}(e+1)$, the pullback $(F_k).\mathrm{comap}$ along `ι ϖ e i` is the ideal sheaf on the affine chart attached, via the inverse of `Scheme.ΓSpecIso`, to the ideal $(\mathrm{V}\,\varpi)$ if $k = i$, to $(\mathrm{U}\,\varpi)$ if $k = i+1$, and to the unit ideal otherwise, where `U ϖ` and `V ϖ` are the two coordinate elements of `CrossingQuotient O ϖ`. Let $t : \operatorname{Spec} O \to$ `Resolution ϖ e` be a section of the structure morphism, i.e. $t$ followed by `Resolution.toSpec ϖ e` is the identity, and let $d$ be a natural number with $0 < d < e$ such that the image under $t$ of the closed point of $O$ lies in the support of $F_d$ and in the support of no $F_k$ with $k \neq d$. Then $t$ is a closed immersion, and there is a unit $\alpha \in O^\times$ such that $t$ equals $\operatorname{Spec}$ of the $O$-algebra map `CrossingQuotient.lift` sending $X_0 \mapsto \varpi\alpha^{-1}$ and $X_1 \mapsto \alpha$ (legitimate since $(\varpi\alpha^{-1})\alpha = \varpi$), followed by the chart inclusion `ι ϖ e ⟨d - 1, _⟩`.
--
--   This is the classification of the $O$-points of the resolved local model $uv = \varpi^{e}$ that meet the open part of a single exceptional line: such a section is the point "$X_1 = \alpha$" of the chart numbered $d-1$, for a unit $\alpha$, and in particular is a closed immersion. It is used by [`MvPolynomial.CrossingQuotient.Resolution.specialFibrePackage_of_chartTable`](thm.html#MvPolynomial.CrossingQuotient.Resolution.specialFibrePackage_of_chartTable) in the bookkeeping of components and divisors on the special fibre. The proof cites the separatedness statement [`MvPolynomial.CrossingQuotient.Resolution.isSeparated`](thm.html#MvPolynomial.CrossingQuotient.Resolution.isSeparated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤)))
    (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e) (ht : t ≫ Resolution.toSpec ϖ e = 𝟙 _)
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (hmem : t.base (IsLocalRing.closedPoint O) ∈ (F ⟨d, by omega⟩).support)
    (hnot : ∀ k : Fin (e + 1), (k : ℕ) ≠ d → t.base (IsLocalRing.closedPoint O) ∉ (F k).support) :
    IsClosedImmersion t ∧ ∃ α : Oˣ, t =
      Spec.map (CommRingCat.ofHom (CrossingQuotient.lift ϖ (ϖ * ((α⁻¹ : Oˣ) : O)) (α : O)
        (by rw [mul_assoc, Units.inv_mul, mul_one]; rfl)).toRingHom) ≫ Resolution.ι ϖ e ⟨d - 1, by omega⟩ := by sorry
