-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_22
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_22
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:13:50.348461+00:00
-- url     : https://prove2.me/theorems/0eb7d7ed-ef52-41c6-8b1b-76af3a36391b
-- title:
--   Sidorenko construction: Tail, Discriminant, batch 22
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Tail.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Discriminant.lean; source propositions actualSingularTail_nonneg, actualSingularTail_bound, radicalQuotientForm_mk, radicalQuotientForm_nondegenerate, radicalQuotientForm_isSymm, form_isSymm_neg, radicalQuotientForm_neg, discriminantSign_ne_zero, discriminantSign_sq, discriminantSign_cases, determinant_character_basis_independent, determinant_character_basis_independent_indices, discriminantSign_eq, discriminantSign_neg, pullback_isSymm, pullback_ker, pullbackQuotientEquiv_mk, pullbackQuotientForm, discriminantSign_pullback, matrix_bilin_eval, matrix_bilin_ker, matrix_radical_quotient_rank, matrix_rank_neg, exists_matrix_of_nonsingular, exists_matrix_rank_sign, matrixSign_neg, mem_signedLayer, signedLayer_nonempty, layerMass_pos, rankKernel_nonneg, neg_mem_signedLayer, signedLayer_card_neg, rankKernel_neg, uniformMean_rankKernel, range_sup_complement, complementary_rank_iff, matrix_complementary_rank_iff, half_rank_projection, symmetricBorder_det, uniformMean_congr.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_22
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0591]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0609]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0613] :
  OAI.SidorenkoCounterexample.ProofCertificate_0614 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0615 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0616 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0617 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0618 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0619 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0620 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0621 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0622 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0623 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0624 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0625 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0626 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0627 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0628 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0629 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0630 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0631 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0632 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0633 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0634 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0635 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0636 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0637 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0638 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0639 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0640 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0641 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0642 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0643 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0644 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0645 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0646 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0647 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0648 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0649 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0650 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0651 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0652 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0653 := by sorry
