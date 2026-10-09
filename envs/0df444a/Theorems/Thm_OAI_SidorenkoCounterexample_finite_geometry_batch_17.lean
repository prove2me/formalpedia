-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_17
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_17
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:12:19.084275+00:00
-- url     : https://prove2.me/theorems/1439955e-e6c9-4a7c-a704-16a881559b12
-- title:
--   Sidorenko construction: PairBounds, Exposure, batch 17
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/PairBounds.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Exposure.lean; source propositions dualGraph_pair_kernel_ge, canonicalPairCoding_injective, dualPairForms_card, center_stratum_square, dualPairLift_probability_bound, pairPlanted_bound_one, two_active_gain_bound, canonical_center_pair_probability_bound, canonical_center_pair_gain_bound, pairCenter_profile_card, symplectic_center_stratum_card_eq, symplectic_center_pair_gain_bound, pairFaceDensity_nonneg, normalized_pair_gain, pairFaceDensity_gain_bound, actual_profile_pair_sum_le, validSeq_card_bound, faceVertex_correct, classPoint_bijective, classFace_injective, classOldZero_lt, classOldOne_lt, classRoot_correct, classStep_correct, classOldPair_correct, classNewPairZero_correct, classNewPairOne_correct, classParent_lt, classOldPair_parent, classOldPair_injective, classFace_occurs, classInternal_occurs, classOldPair_internal, classStep_pairs, classStep_pairs_distinct, faceVertex_injective, faceVertex_pairs, classRootPairZero, classRootPairOne, classRootPairTwo, classTree_occurs, inverse_power_inequality, tripleProfile_card_raw, conditionalProfile_card_raw.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_17
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0007]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0021]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0031]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0035]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0036]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0082]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0097]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0098]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0100]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0148]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0296]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0298]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0299]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0302]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0305]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0310]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0311]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0314]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0332]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0414]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0417]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0420]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0421] :
  OAI.SidorenkoCounterexample.ProofCertificate_0422 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0423 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0424 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0425 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0426 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0427 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0428 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0429 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0430 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0431 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0432 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0433 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0434 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0435 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0436 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0437 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0438 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0439 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0440 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0441 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0442 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0443 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0444 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0445 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0446 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0447 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0448 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0449 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0450 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0451 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0452 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0453 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0454 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0455 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0456 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0457 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0458 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0459 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0460 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0461 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0462 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0463 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0464 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0465 := by sorry
