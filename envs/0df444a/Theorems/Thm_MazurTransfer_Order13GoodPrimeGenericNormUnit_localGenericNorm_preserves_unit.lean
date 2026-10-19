-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormUnit_localGenericNorm_preserves_unit
-- name    : MazurTransfer.Order13GoodPrimeGenericNormUnit.localGenericNorm_preserves_unit
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T04:55:06.419359+00:00
-- url     : https://prove2.me/theorems/8537dc3a-bcdf-4c89-a7e9-c9c2b2a15a68
-- title:
--   Transported actual Picard endomorphisms preserve the generic local unit
-- statement:
--   Let $q$ be a prime not dividing $104$, and let $\phi$ be an internal group endomorphism of the original rational Picard scheme. Transport $\phi$ through the canonical group-scheme isomorphism to the generic fibre of the selected local Picard model, obtaining $\phi_{\mathrm{loc}}$. If $e$ is the unit section for the generic local group law, then
--
--   $$\phi_{\mathrm{loc}}\circ e=e.$$
--
--   This proves unit preservation for every such transported endomorphism, including the two actual nineteen-norm maps, without an additional assumption on the residue characteristic.
-- source:
--   MazurTheorem, Order13GoodPrimeGenericNormUnit.lean, complete original theorem and hypotheses, full source SHA-256 86fcbcad9890fb5bffa0374aacb8e3d0387f2f917d4161734518e5ba6f67c2b2, Apache-2.0. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
import Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalGenericGroupIdentity_generic_group_law_units_equal
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup

theorem MazurTransfer.Order13GoodPrimeGenericNormUnit.localGenericNorm_preserves_unit (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    NeronModelInfra.schemeHomOverComp ((genericLocalLaw q hq).one (𝟙 _))
      (localGenericNorm q hq φ) = (genericLocalLaw q hq).one (𝟙 _) := by sorry
