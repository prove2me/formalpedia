-- Prove2me | Theorems.Thm_GroundTheory_Arith_Jacobian_ker_le_span_of_spanFinrank_le
-- name    : GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:08.145704+00:00
-- url     : https://prove2.me/theorems/527ff9e4-d92f-4783-9219-f9a17411d2f6
-- title:
--   Jacobian: ker le span of span Finrank le
-- statement:
--   The Jacobian construction uses the ker le span of span Finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/SmoothOfRegular.lean#L149-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/SmoothOfRegular.lean#L149-L199

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Jacobian
open IsLocalRing TensorProduct
universe u
noncomputable section
variable {k : Type u} [Field k] {P S : Type u} [CommRing P] [CommRing S] [Algebra k P]
  [Algebra k S] [Algebra P S] [IsScalarTower k P S] [IsLocalRing P] [IsLocalRing S]
variable (hsurj : Function.Surjective (algebraMap P S))
  (hres : Function.Surjective (algebraMap k (ResidueField S)))
variable [IsNoetherianRing P]
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S]
include hsurj

theorem GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le {κ : Type} [Fintype κ] (f : κ → P)
    (hfI : ∀ i, f i ∈ RingHom.ker (algebraMap P S))
    (hcov : RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2)
    (d : ℕ) (hμ : (maximalIdeal S).spanFinrank ≤ d) (hdim : (d : WithBot ℕ∞) ≤ ringKrullDim S) :
    RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) := by sorry
