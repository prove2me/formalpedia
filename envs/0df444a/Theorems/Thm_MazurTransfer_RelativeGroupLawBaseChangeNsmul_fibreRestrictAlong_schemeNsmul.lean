-- Prove2me | Theorems.Thm_MazurTransfer_RelativeGroupLawBaseChangeNsmul_fibreRestrictAlong_schemeNsmul
-- name    : MazurTransfer.RelativeGroupLawBaseChangeNsmul.fibreRestrictAlong_schemeNsmul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T04:41:50.636349+00:00
-- url     : https://prove2.me/theorems/902b3df1-8415-4c2b-bd98-b626571783e8
-- title:
--   Scalar multiplication commutes with arbitrary base change
-- statement:
--   Let $R$ and $R^\prime$ be commutative rings, let $\iota:\operatorname{Spec}R^\prime\to\operatorname{Spec}R$ be a base morphism, and let $G$ be a relative group law on a scheme over $R$. For every natural number $n$, restricting its scalar endomorphism to the base change gives the scalar endomorphism of the base-changed group law:
--
--   $$\iota^*([n]_G)=[n]_{\iota^*G}.$$
--
--   This holds for arbitrary base change and is used to identify the generic restriction of multiplication by nineteen on the selected local Picard model.
-- source:
--   MazurTheorem, RelativeGroupLawBaseChangeNsmul.lean, original scalar compatibility theorem and complete induction helper; full source SHA-256 a191a4251421580f68d8d3c65184495fbdcda0b33c1ed3f2df95cace02cac7a5, Apache-2.0. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian NeronSpecialFibreInfra

theorem MazurTransfer.RelativeGroupLawBaseChangeNsmul.fibreRestrictAlong_schemeNsmul {R R' : Type u} [CommRing R] [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) :
    fibreRestrictAlong ι f f ⟨G.schemeNsmul n, G.schemeNsmul_over n⟩ =
      ⟨(G.baseChange ι).schemeNsmul n, (G.baseChange ι).schemeNsmul_over n⟩ := by sorry
