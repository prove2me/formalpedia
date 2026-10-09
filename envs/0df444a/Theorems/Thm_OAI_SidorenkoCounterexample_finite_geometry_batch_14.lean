-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_14
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_14
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:15:15.319689+00:00
-- url     : https://prove2.me/theorems/720078fa-76b0-44ac-ae1c-721eab05a7f0
-- title:
--   Sidorenko construction: Planted, Coercivity, batch 14
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Planted.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Coercivity.lean; source propositions fixedCommonCenter_injection, reducedPlantedSum_nonneg, symplectic_center_profile_card_upper, fixedCommonCenter_card_upper, profileCenter_injection, unweight_count_bound, fixedCommonCenter_card_rpow_upper, commonData_fixed_card_upper, commonPlantedTerm_nonneg, profileCenter_card_upper, normalized_count_ratio_bound, orbit_member_profile, orbitCenter_profile_injection, orbit_center_count_le_profile, tripleFaceDensity_nonneg, symplectic_center_stratum_card_pos, tripleFaceDensity_profile_bound, tripleFaceDensity_full_bound, quadratic_ge_right, quadratic_ge_endpoints, coercivity_scalar_pos, coercivity_scalar_neg, coercivity_scalar, three_sq.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_14
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0281]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0282]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0294]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0295]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0301]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0307]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0309]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0311]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0313]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0315] :
  OAI.SidorenkoCounterexample.ProofCertificate_0317 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0318 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0319 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0320 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0321 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0322 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0323 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0324 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0325 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0326 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0327 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0328 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0329 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0330 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0331 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0332 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0333 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0334 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0335 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0336 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0337 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0338 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0339 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0340 := by sorry
