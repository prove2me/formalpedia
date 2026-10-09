-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_13
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_13
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:19:13.866468+00:00
-- url     : https://prove2.me/theorems/03c27719-4eae-4de3-8235-a8ea0af64e23
-- title:
--   Sidorenko construction: OrbitBounds, Planted, batch 13
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/OrbitBounds.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Planted.lean; source propositions fixedCommonProfile_injection, fixedCommonProfile_card_upper, fullProfileConstant_pos, tripleProfile_card_upper, symplectic_pair_count, symplectic_pair_card_bounds, orderedPairDim_card_lower, pairCompletion_card_congr, tripleProfile_completion_card, conditionalProfile_card_upper, reduceSubspace_finrank_general, reduce_center_intersection_finrank, tripleCenter_orbit_card, tripleCenterOrbit_card, exists_center_coordinates, map_pair_finrank, map_common_zero_iff, symplectic_center_profile_probability_bound, symplectic_profile_pair_sum_le, commonCenter_card_upper, commonCenter_cost_bound.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_13
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0010]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0013]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0031]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0034]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0038]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0106]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0148]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0271]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0273]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0291]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0292]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0293]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0294]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0295] :
  OAI.SidorenkoCounterexample.ProofCertificate_0296 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0297 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0298 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0299 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0300 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0301 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0302 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0303 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0304 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0305 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0306 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0307 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0308 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0309 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0310 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0311 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0312 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0313 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0314 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0315 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0316 := by sorry
