-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_11
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_11
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:01:45.69885+00:00
-- url     : https://prove2.me/theorems/729dff9d-8805-4dba-b6a5-8110ee564079
-- title:
--   Sidorenko construction: Configurations, batch 11
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Configurations.lean; source propositions containmentOrbitFiber_card_lower, exists_isotropic_isometry_extension, triplePair_inter_own, triplePairSum_split_all, triplePair_inter_all, ownAvoidanceOrbitFiber_pairs, subspace_map_extension, subtype_map_comap_of_le, subspace_comap_sup_of_le, triple_subspace_orbit_injection, fullTripleOrbit_fixedPair_injection, fullTripleOrbit_fixedPair_card_lower, triple_isotropic_orbit_card_lower, fixedPairTripleOrbit_card_lower, pair_cost_cancellation, common_cost_cancellation, finrank_sup_of_disjoint, triplePairSum_finrank, triplePairSum_inter_finrank, pairOrbitConstant_pos, commonZeroOrbit_card_lower.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates08

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_11
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0012]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0127]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0137]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0139]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0181]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0219]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0226]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0228]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0238]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0241]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0242]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0243]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0249]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0251]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0255] :
  OAI.SidorenkoCounterexample.ProofCertificate_0256 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0257 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0258 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0259 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0260 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0261 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0262 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0263 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0264 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0265 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0266 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0267 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0268 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0269 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0270 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0271 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0272 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0273 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0274 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0275 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0276 := by sorry
