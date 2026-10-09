-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_21
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_21
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:15:43.577147+00:00
-- url     : https://prove2.me/theorems/288aa032-50d5-47ff-8377-dfefc7b2d3b8
-- title:
--   Sidorenko construction: Tail, batch 21
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Tail.lean; source propositions residualDirectConstant_nonneg, residualNondirectConstant_nonneg, pairDimProfile_card_split, pairDimProfile_residual_card_bound, pointProfile_card_le_pair, normalizedPointProfileCount_nonneg, lagrangianRealCard_pos, normalizedPointProfileCount_exposure, normalizedPointProfileCount_residual, residual_triangular_sum_le, singular_triangular_sum_pos, globalTail_dichotomy, profileTermMajorant_nonneg, negative_rpow_tendsto_zero, profileTermMajorant_tendsto_zero, residual_gain_bound, normalizedPointProfile_term_bound, profileTailMajorant_tendsto_zero, normalizedPointProfile_product_bound, activeFaceDensity_nonneg, lagrangian_card_pos, activeFaceDensity_empty, activeFaceDensity_singleton, activeFaceDensity_pair, activeFaceDensity_full, one_le_lowerTailMajorant, fin3_subsets, activeFaceDensity_lower_bound, activeFaceDensity_tail_bound, profileActiveDensity_nonneg, profileActiveDensity_bound, profileTailMajorant_nonneg, integratedTailMajorant_tendsto_zero, singularTailThreshold_large, singularTailThreshold_dichotomy, profileActiveDensity_tail_bound, integratedActiveTail_nonneg, integratedActiveTail_bound, finite_inf_lagrangians_finrank_le, configProfile_property, configProfile_eq_iff, actualSingularTail_eq_integrated.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_21
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0298]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0332]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0349]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0350]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0371]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0372]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0410]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0432]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0478]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0537]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0542]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0548]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0552]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0557]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0559]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0562]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0563]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0565]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0566]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0568]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0569]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0570]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0571] :
  OAI.SidorenkoCounterexample.ProofCertificate_0572 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0573 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0574 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0575 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0576 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0577 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0578 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0579 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0580 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0581 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0582 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0583 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0584 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0585 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0586 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0587 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0588 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0589 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0590 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0591 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0592 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0593 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0594 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0595 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0596 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0597 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0598 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0599 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0600 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0601 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0602 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0603 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0604 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0605 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0606 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0607 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0608 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0609 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0610 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0611 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0612 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0613 := by sorry
