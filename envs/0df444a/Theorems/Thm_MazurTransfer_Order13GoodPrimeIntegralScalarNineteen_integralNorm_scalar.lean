-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralScalarNineteen_integralNorm_scalar
-- name    : MazurTransfer.Order13GoodPrimeIntegralScalarNineteen.integralNorm_scalar
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T05:15:57.656555+00:00
-- url     : https://prove2.me/theorems/043bda16-a44e-4c82-8129-c9e31d1403be
-- title:
--   Integral extension preserves every scalar multiplication map
-- statement:
--   Let $q$ be a prime with $q \nmid 104$. Let $\mathcal J_q$ be the selected local Picard model over $\mathbb Z_{(q)}$, with its actual relative group law, and identify its rational generic fibre with the original rational Picard scheme by the canonical comparison. For every natural number $n$, the unique integral extension of rational multiplication by $n$ is multiplication by $n$ for this same local group law:
--
--   $$\operatorname{Ext}_q([n]_{\mathbb Q})=[n]_{\mathcal J_q}.$$
--
--   In particular, taking $n=19$ identifies the integral scalar extension occurring in both actual norm composites with the local multiplication-by-nineteen morphism. The equality itself imposes no additional restriction $q\ne19$.
-- source:
--   MazurTheorem, Order13GoodPrimeIntegralScalarNineteen.lean, complete original theorem and original helper contracts; full source SHA-256 9051388adcfa1a4e90b820b12326aae435823a8c1c2ebbddd2e742c43ed7120d, Apache-2.0. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormCompositionData
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalGenericGroupConstructorData
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeLocalPicardModels
open Order13ActualPicardDiamondSchemeEndomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison.actualGroup

theorem MazurTransfer.Order13GoodPrimeIntegralScalarNineteen.integralNorm_scalar (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (n : ℕ) :
    integralNorm q hq ((𝟙 (Over.mk actualPicard.toBase)) ^ n) =
      ⟨(localLaw q hq).schemeNsmul n, (localLaw q hq).schemeNsmul_over n⟩ := by sorry
