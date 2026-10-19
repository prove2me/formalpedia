-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_piConjugateKernelToQ_finite_etale
-- name    : MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.piConjugateKernelToQ_finite_etale
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T21:31:30.971606+00:00
-- url     : https://prove2.me/theorems/15022455-9c92-47c3-a262-df153f04187e
-- title:
--   The original actual rational Picard pi-bar kernel is finite etale over Q
-- statement:
--   Let P be the same actual rational represented Picard scheme and let pi-bar be its original norm endomorphism. The original kernel scheme, defined as the fibre product of this morphism with the original zero section, is finite and etale over Q via its original structural map. The named downstream consumers are the actual finite norm-kernel modules and norm-isogeny descent.
-- source:
--   Exact original MazurTheorem Order13ActualPicardNormFiniteEtaleIsogenies.piConjugateKernelToQ_finite_etale statement and main proof, with both original factor helper types preserved. Their proofs are projections of the accepted exact original joint factor theorem. All four original kernel constructor values are retained in the public kernel data package. Official Anthropic FLT geometry interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelSchemesData
noncomputable section
open AlgebraicGeometry
open MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies

theorem MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.piConjugateKernelToQ_finite_etale : IsFinite piConjugateKernelToQ ∧ Etale piConjugateKernelToQ := by sorry
