-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_18
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_18
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:14:21.836471+00:00
-- url     : https://prove2.me/theorems/a3ab7ef7-3110-4694-80a4-3cf6a35ba117
-- title:
--   Sidorenko construction: Exposure, batch 18
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Exposure.lean; source propositions root_natural_cost, step_natural_cost, PointProfile.local, classStepBound_nonneg, classStep_card_bound, classPrefix_valid, classRoot_card_bound, classStepBound_product, pointProfile_class_card_bound, sum_class_faces, sum_class_old_pairs, sum_class_exponent, pointProfile_card_bound, zeroValidSeq_card_bound, orthogonalSeq_independent, orthogonalTuple_valid, independent_orthogonal_card, orthogonalStep_card_bound, orthogonalTuple_card_bound, sum_priorConstraintCount, orthogonalTuple_card_rpow, nat_card_subtype_sum, double_constraintPairCount, enumeratedRelation_symm, constrainedTuple_card_rpow, independentTuples_card_lower, containingLagrangian_card_rpow, familySpanCoding_injective, familySpan_card_upper, directFamilyBases_independent.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_18
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0000]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0298]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0374]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0383]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0414]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0438]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0440]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0442]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0443]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0444]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0445]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0446]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0447]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0448]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0452]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0455]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0456]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0459]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0460]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0461]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0462]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0464]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0465] :
  OAI.SidorenkoCounterexample.ProofCertificate_0466 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0467 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0468 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0469 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0470 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0471 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0472 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0473 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0474 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0475 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0476 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0477 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0478 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0479 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0480 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0481 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0482 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0483 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0484 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0485 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0486 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0487 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0488 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0489 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0490 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0491 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0492 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0493 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0494 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0495 := by sorry
