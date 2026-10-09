-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_31
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_31
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:18:55.773212+00:00
-- url     : https://prove2.me/theorems/a15677eb-d98c-4d32-8efd-e99c32b897a2
-- title:
--   Sidorenko construction: Charts, GlobalMoments, batch 31
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Charts.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/GlobalMoments.lean; source propositions bool_indicator_expansion, bool_law_expansion, uniformMean_test_fibers, boolean_law_tendsto, boolean_test_tendsto, pairBool_test_tendsto, uniformMean_two_differences, faceBound_one, faceLocal_nonneg, faceLocal_bound, pairPolynomial_abs_le, facePolynomial_abs_le, faceBound_tendsto, faceError_mean_tendsto, canonicalKernel_nonneg, rankKernel_chart_bound, canonicalKernel_prod, canonicalKernel_mean, faceLocal_chart_bound, facePair_endpoints, modelPair_mem, face_pairs_image, modelPair_all, fullTransverse_face, pairBool_eq_sign, facePolynomial_bool, configurationProduct_nonneg, canonicalSingular_chart, canonicalConfiguration_nonneg, configuration_chart_bound, actualSingularTail_uniform, matrixSingularTail_bound, canonicalTail_tendsto, matrixSingularTail_tendsto, globalBound_eight.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleB

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_31
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0013]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0034]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0198]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0372]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0591]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0598]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0604]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0605]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0614]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0615]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0643]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0661]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0664]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0813]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0814]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0815]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0816]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0824]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0827]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0856]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0857]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0859]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0860]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0890]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0898]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0920]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0927]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0929]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_0930]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_0931]
  [p41 : OAI.SidorenkoCounterexample.ProofCertificate_0932]
  [p42 : OAI.SidorenkoCounterexample.ProofCertificate_0933]
  [p43 : OAI.SidorenkoCounterexample.ProofCertificate_0934]
  [p44 : OAI.SidorenkoCounterexample.ProofCertificate_0935]
  [p45 : OAI.SidorenkoCounterexample.ProofCertificate_0938]
  [p46 : OAI.SidorenkoCounterexample.ProofCertificate_0940]
  [p47 : OAI.SidorenkoCounterexample.ProofCertificate_0941]
  [p48 : OAI.SidorenkoCounterexample.ProofCertificate_0942]
  [p49 : OAI.SidorenkoCounterexample.ProofCertificate_0943]
  [p50 : OAI.SidorenkoCounterexample.ProofCertificate_0944]
  [p51 : OAI.SidorenkoCounterexample.ProofCertificate_0946]
  [p52 : OAI.SidorenkoCounterexample.ProofCertificate_0950]
  [p53 : OAI.SidorenkoCounterexample.ProofCertificate_0952] :
  OAI.SidorenkoCounterexample.ProofCertificate_0953 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0954 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0955 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0956 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0957 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0958 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0959 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0960 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0961 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0962 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0963 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0964 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0965 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0966 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0967 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0968 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0969 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0970 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0971 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0972 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0973 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0974 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0975 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0976 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0977 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0978 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0979 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0980 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0981 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0982 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0983 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0984 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0985 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0986 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0987 := by sorry
