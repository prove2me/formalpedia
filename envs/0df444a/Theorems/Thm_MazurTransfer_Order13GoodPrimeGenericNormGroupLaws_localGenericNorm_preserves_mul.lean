-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeGenericNormGroupLaws_localGenericNorm_preserves_mul
-- name    : MazurTransfer.Order13GoodPrimeGenericNormGroupLaws.localGenericNorm_preserves_mul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T05:22:59.002981+00:00
-- url     : https://prove2.me/theorems/71ace6d3-d35e-4493-b0dd-1e303c4052e5
-- title:
--   Transported actual Picard endomorphisms preserve generic local multiplication
-- statement:
--   Let $q$ be a prime not dividing $104$, and let $\phi$ be an internal group endomorphism of the original rational Picard scheme. Transport it through the canonical group-scheme comparison to the generic fibre of the selected local Picard model, obtaining $\phi_{\mathrm{loc}}$. For every scheme $T$ over $\mathbb Q$ and every two $T$-points $x,y$ of that generic fibre,
--
--   $$\phi_{\mathrm{loc}}(x+y)=\phi_{\mathrm{loc}}(x)+\phi_{\mathrm{loc}}(y),$$
--
--   where addition is the generic fibre of the actual local integral group law. This is the pointwise multiplication compatibility used to descend the same actual norm maps to integral group endomorphisms.
-- source:
--   MazurTheorem, Order13GoodPrimeGenericNormGroupLaws.lean, complete original theorem and original helper contracts; full source SHA-256 27a46b8447e29fb75044ed0da6160be98e53de8d0288f9d1da7231ff39f9705d, Apache-2.0. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalGenericGroupIdentity Order13GoodPrimeLocalGenericPicardComparison
open Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup

theorem MazurTransfer.Order13GoodPrimeGenericNormGroupLaws.localGenericNorm_preserves_mul (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (localGenericPicard q hq).toBase) :
    NeronModelInfra.schemeHomOverComp ((genericLocalLaw q hq).mul t x y)
      (localGenericNorm q hq φ) =
    (genericLocalLaw q hq).mul t
      (NeronModelInfra.schemeHomOverComp x (localGenericNorm q hq φ))
      (NeronModelInfra.schemeHomOverComp y (localGenericNorm q hq φ)) := by sorry
