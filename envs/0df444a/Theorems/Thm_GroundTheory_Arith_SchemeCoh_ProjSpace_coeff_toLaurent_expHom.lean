-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_coeff_toLaurent_expHom
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.coeff_toLaurent_expHom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:52.598003+00:00
-- url     : https://prove2.me/theorems/3ecf6425-fd72-491a-b06a-81826748ea9e
-- title:
--   Proj Space: coeff to Laurent exp Hom
-- statement:
--   The Proj Space construction uses the coeff to Laurent exp Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L186-L188

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.coeff_toLaurent_expHom (a : MvPolynomial (Fin (n + 1)) A) (e : Fin (n + 1) →₀ ℕ) :
    (toLaurent A n a).coeff (expHom n e) = a.coeff e := by sorry
