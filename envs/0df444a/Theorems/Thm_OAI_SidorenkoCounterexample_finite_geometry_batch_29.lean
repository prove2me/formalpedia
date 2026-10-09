-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_29
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_29
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:20:02.033585+00:00
-- url     : https://prove2.me/theorems/91262bed-6648-483e-baa4-b60d115a141b
-- title:
--   Sidorenko construction: SignMoments, Monomials, batch 29
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/SignMoments.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Monomials.lean; source propositions characterProduct_abs_le, characterProduct_sum, bounded_test_l1, quadraticMap_character_moment, matrix_form_rank, schur_polynomial, inverse_form_span_rank, schur_sign_moment, matrix_combination_form_rank, matrix_low_rank_span_bound, badMinors_bound, starDifference_surjective, uniformMean_starDifference, symmetricBorder_sub, uniformMean_pi_prod, uniformMean_bordered, starSign_abs_le, starSign_update_bound, testedStar_update_bound, testedStar_mean_bound, pair_endpoints, pair_endpoints_ne, pairOther_ne, pair_vertices_other, selectedIncident_card, pairOther_injective, pairSign_abs_le, determinant_difference_even, pairSign_other, pairSign_product_abs_le, nonincidentProduct_abs_le, nonincidentProduct_update, pairSign_product_split, pairSign_moment_bound, minorBadBound_tendsto.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleB

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_29
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0051]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0373]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0510]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0633]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0635]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0636]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0652]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0654]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0655]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0660]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0662]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0663]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0664]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0678]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0715]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0754]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0787]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0824]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0825]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0826]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0829]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0873]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0877] :
  OAI.SidorenkoCounterexample.ProofCertificate_0878 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0879 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0880 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0881 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0882 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0883 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0884 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0885 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0886 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0887 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0888 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0889 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0890 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0891 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0892 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0893 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0894 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0895 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0896 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0897 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0898 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0899 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0900 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0901 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0902 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0903 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0904 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0905 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0906 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0907 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0908 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0909 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0910 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0911 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0912 := by sorry
