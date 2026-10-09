-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_16
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_16
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:14:24.096611+00:00
-- url     : https://prove2.me/theorems/204863be-5dd2-420c-bc63-4d6cc31299d6
-- title:
--   Sidorenko construction: Coercivity, PairBounds, batch 16
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Coercivity.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/PairBounds.lean; source propositions global_tail_pair_bound, tailRemainderBound_nonneg, tailSlack_linear, tailLinear_nonneg, tailLinear_half, tailRemainder_bounded, tailSlack_lower_nonneg, global_maxH_bound, eventually_integer_regime, delta_integer_regime, tailSlack_integer, integer_slack_classification, full_zero_face_residue, lower_zero_face_residue, FaceResidue.one_iff, pair_incidence_card, sum_face_pairs, residue_root_zero, residue_propagation, uniform_tail_dichotomy, plantedTailTuple_s, plantedTailTuple_feasible, fullPlantedExponent_eq, real_card_sigma_le, pairFormDifference_surjective, pairFormDifference_graph, pairFormDifference_nullity_bound, pairBaseCode_injective, subspacePairProfile_card_upper, subspacePairProfile_probability_bound, dualGraph_pair_kernel_exact.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_16
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0011]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0042]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0045]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0059]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0071]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0219]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0345]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0346]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0347]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0348]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0355]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0356]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0357]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0358]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0359]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0360]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0363]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0368]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0369]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0375]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0378]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0379]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0380]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0386]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0387]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0388]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0389]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0390] :
  OAI.SidorenkoCounterexample.ProofCertificate_0391 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0392 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0393 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0394 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0395 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0396 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0397 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0398 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0399 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0400 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0401 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0402 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0403 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0404 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0405 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0406 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0407 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0408 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0409 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0410 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0411 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0412 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0413 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0414 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0415 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0416 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0417 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0418 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0419 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0420 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0421 := by sorry
