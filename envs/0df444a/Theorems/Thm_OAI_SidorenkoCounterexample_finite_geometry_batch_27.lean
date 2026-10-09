-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_27
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_27
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:19:51.235989+00:00
-- url     : https://prove2.me/theorems/2279426e-c832-4b8c-a003-84d6dd641541
-- title:
--   Sidorenko construction: LocalMoments, batch 27
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/LocalMoments.lean; source propositions uniformMean_mul_card, restrictionSign_count, pairCenter_card, tripleCenter_card, pair_exponent_cancel, triple_exponent_cancel, pairCoefficient_normalized, tripleCoefficient_normalized, pairCoefficient_nonneg, tripleCoefficient_nonneg, pairCoefficient_tendsto, tripleCoefficient_tendsto, maxOrthogonal_card_lower, halfIsotropic_card, pairFamily_card_ge, isotropicFamily_card_ge, matrix_restriction_family_L1, pairRestrictionFraction_L1, isotropicRestrictionFraction_L1, uniformMean_sum, uniformMean_coordinate, uniformMean_update, uniformMean_mul_right, uniformMean_ite_le, symmetricInverse_involutive, pairLocal_card, tripleLocal_card, pairLocal_match, pairLocal_mismatch, tripleLocal_mismatch, inverse_difference_det, inverse_difference_nondegenerate, matching_inverse_difference_split, tripleLocal_match, uniformMean_le_one, uniformMean_subLeft, pairRestrictionFraction_range, isotropicRestrictionFraction_range, uniformMean_inverse.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleB

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_27
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0006]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0640]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0661]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0663]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0664]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0683]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0718]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0719]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0724]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0725]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0728]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0731]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0732]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0736]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0739]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0745]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0754]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0767]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0770]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0773]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0775]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0776]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0784]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0786]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0788]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0789]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0791]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0793]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_0796]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_0797]
  [p41 : OAI.SidorenkoCounterexample.ProofCertificate_0799]
  [p42 : OAI.SidorenkoCounterexample.ProofCertificate_0800]
  [p43 : OAI.SidorenkoCounterexample.ProofCertificate_0801]
  [p44 : OAI.SidorenkoCounterexample.ProofCertificate_0802]
  [p45 : OAI.SidorenkoCounterexample.ProofCertificate_0803]
  [p46 : OAI.SidorenkoCounterexample.ProofCertificate_0804] :
  OAI.SidorenkoCounterexample.ProofCertificate_0805 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0806 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0807 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0808 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0809 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0810 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0811 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0812 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0813 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0814 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0815 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0816 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0817 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0818 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0819 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0820 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0821 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0822 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0823 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0824 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0825 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0826 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0827 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0828 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0829 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0830 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0831 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0832 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0833 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0834 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0835 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0836 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0837 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0838 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0839 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0840 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0841 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0842 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0843 := by sorry
