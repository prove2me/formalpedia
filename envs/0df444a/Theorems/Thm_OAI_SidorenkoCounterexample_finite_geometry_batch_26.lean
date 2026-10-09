-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_26
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_26
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:18:48.742036+00:00
-- url     : https://prove2.me/theorems/6faad202-cc62-4c16-bd09-046b60e41c9f
-- title:
--   Sidorenko construction: Restrictions, Normalization, batch 26
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Restrictions.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Normalization.lean; source propositions restriction_family_L1_sq, update_vec_zero, update_vec_one, altForm_card, canonicalOrthogonal_apply, canonicalOrthogonal_symm, canonicalOrthogonal_nondegenerate, maxOrthogonal_finrank, formGraph_orthogonal_isotropic, graphMaxOrthogonal_form_injective, maxOrthogonal_pairing_zero, graphMaxOrthogonal_surjective, maxOrthogonal_card_sum, canonicalOrthogonal_matrix, hyperbolic_block_det, canonicalOrthogonal_sign, split_form_equivalent, split_form_card, grassmann_single_factor, subspace_count_normalized, inverse_power_tendsto_zero, grassmannFactor_tendsto, triangular_nat_add, layerMass_normalized, primeInfinity_real_tendsto, symmetricSignProb_tendsto, layerMass_tendsto, maxOrthogonal_card_by_dimension, choose_two_add, maxOrthogonal_normalized, orthogonalFactor_tendsto, split_form_normalized, signed_pair_compatibility, signed_second_iff, centerSubspaceEquiv_rank, centerSubspaceEquiv_sign, restrict_eq_zero_iff_isotropic, half_isotropic_iff_self.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleB

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_26
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0004]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0621]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0636]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0639]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0651]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0682]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0683]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0697]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0714]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0724]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0725]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0726]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0727]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0728]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0730]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0731]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0732]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0733]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0736]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0740]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0746]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0764]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0766] :
  OAI.SidorenkoCounterexample.ProofCertificate_0767 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0768 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0769 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0770 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0771 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0772 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0773 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0774 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0775 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0776 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0777 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0778 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0779 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0780 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0781 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0782 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0783 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0784 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0785 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0786 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0787 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0788 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0789 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0790 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0791 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0792 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0793 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0794 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0795 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0796 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0797 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0798 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0799 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0800 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0801 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0802 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0803 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0804 := by sorry
