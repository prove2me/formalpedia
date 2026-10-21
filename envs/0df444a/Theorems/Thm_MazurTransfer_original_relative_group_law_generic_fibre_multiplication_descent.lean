-- Prove2me | Theorems.Thm_MazurTransfer_original_relative_group_law_generic_fibre_multiplication_descent
-- name    : MazurTransfer.original_relative_group_law_generic_fibre_multiplication_descent
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T05:31:32.44613+00:00
-- url     : https://prove2.me/theorems/a06ae957-a283-4de8-8a84-bff224095a16
-- statement:
--   For the same original relative group laws and original relative morphism over a domain, preservation of multiplication on the original fraction-field generic fibres implies preservation on every original integral test scheme, with the original flat source and separated target hypotheses. All original hypotheses and universes are retained. Named downstream consumer: same actual integral norm multiplication and kernel Hopf group laws.

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem MazurTransfer.original_relative_group_law_generic_fibre_multiplication_descent : ∀ {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] {A B : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)} [Flat f] [IsSeparated g] (G : RelativeGroupLaw R f) (H : RelativeGroupLaw R g) (φ : SchemeHomOver f g), ∀ (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (RelativeGroupLaw.genericFibreStr K f)),
      NeronModelInfra.schemeHomOverComp ((G.genericFibre K).mul t x y)
        (genericFibreRestrict R K g f φ) =
      (H.genericFibre K).mul t
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K g f φ))
        (NeronModelInfra.schemeHomOverComp y (genericFibreRestrict R K g f φ)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f),
NeronModelInfra.schemeHomOverComp (G.mul t x y) φ =
      H.mul t (NeronModelInfra.schemeHomOverComp x φ)
        (NeronModelInfra.schemeHomOverComp y φ) := by sorry
