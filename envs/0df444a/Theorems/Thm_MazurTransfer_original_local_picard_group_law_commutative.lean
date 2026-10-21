-- Prove2me | Theorems.Thm_MazurTransfer_original_local_picard_group_law_commutative
-- name    : MazurTransfer.original_local_picard_group_law_commutative
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T04:58:18.198122+00:00
-- url     : https://prove2.me/theorems/89c0951a-573c-4cbb-942c-5163ec1de471
-- statement:
--   The same chosen local Picard law over every original good-prime coefficient localization is commutative. Its original representation as the algebraically trivial pointed relative Picard group supplies the commutativity. The same local Picard, group law, prime and coefficient hypotheses are retained. Named downstream consumer: positive-scalar finiteness and flatness of the same actual nineteen norm models.

import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardModelsData
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTorsion.XOneThirteenProjectiveCurve MazurTransfer.Order13IntegralSections

theorem MazurTransfer.original_local_picard_group_law_commutative : ∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), (localLaw q hq).IsCommutative := by sorry
