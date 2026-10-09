-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_32
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_32
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:22:20.093481+00:00
-- url     : https://prove2.me/theorems/ed0c6441-ec31-48df-abfc-627e47f96c64
-- title:
--   Sidorenko construction: GlobalMoments, Activation, batch 32
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/GlobalMoments.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Activation.lean; source propositions faceBound_le_global, configuration_difference_bound, transverseDifference_bound, globalBound_tendsto, transverseDifference_tendsto, boolFacePolynomial_abs_le, boolConfiguration_abs_le, configurationPolynomial_bool, boolSingular_bound, configuration_mean_identity, boolSingular_tendsto, configuration_bool_tendsto, mean_congr, mean_const, mean_add, mean_sub, mean_mul, mean_mul_right, mean_sum, mean_finset_sum, mean_nonneg, mean_mono, mean_bound, abs_mean_le, mean_dirac, mean_uniform, mean_prod, mean_swap, independent_mean_product, mean_map_product, mean_mixture, mean_map, mean_tendsto, boolMonomial_asprod, boolMonomial_abs, boolMonomial_mul, boolSign_mean, boolMonomial_mean, boolMonomial_orthog, tiltLaw_mean, tiltLaw_monomial, activationPhi_empty, activationPhi_mul, activationPhi_disjoint, branchLaw_phi, branchLaw_second, baseActivation_zero, activationMoment_empty, activationMoment_disjoint, baseActivation_moment, pairCorners_mem, pairCorners_table_0, pairCorners_table_1, pairCorners_table_2, pairCorners_table_3, pairCorners_table_4, pairCorners_table_5, pairCorners_table_6, pairCorners_table_7, pairCorners_table_8, pairCorners_table_9.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleB

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_32
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0457]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0605]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0658]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0662]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0824]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0915]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0916]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0919]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0924]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0925]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0926]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0948]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0949]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0950]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0960]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0961]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0962]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0964]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0965]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0966]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0976]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0978]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0986]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0987] :
  OAI.SidorenkoCounterexample.ProofCertificate_0988 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0989 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0990 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0991 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0992 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0993 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0994 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0995 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0996 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0997 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0998 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0999 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1000 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1001 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1002 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1003 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1004 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1005 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1006 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1007 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1008 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1009 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1010 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1011 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1012 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1013 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1014 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1015 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1016 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1017 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1018 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1019 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1020 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1021 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1022 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1023 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1024 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1025 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1026 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1027 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1028 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1029 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1030 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1031 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1032 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1033 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1034 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1035 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1036 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1037 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1038 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1039 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1040 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1041 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1042 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1043 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1044 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1045 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1046 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1047 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1048 := by sorry
