-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_10
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_10
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:01:07.566416+00:00
-- url     : https://prove2.me/theorems/b26bd596-8029-4995-9edb-5ea2e6004f7f
-- title:
--   Sidorenko construction: SubspaceCounts, Configurations, batch 10
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/SubspaceCounts.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Configurations.lean; source propositions linearAut_card_upper, pairLinearOrbit_card_bounds, tripleSumEquiv_apply, map_eq_of_restriction_aut, tripleLinearStabilizerRestriction_bijective, tripleLinearOrbit_card_identity, tripleLinearOrbit_card_bounds, uniform_prod_card, uniform_preimage_card, avoidance_exact_intersection, triple_pairs_disjoint, triple_own_avoidance, reduction_intersection_of_split_kernel, symplectic_orderedTransversePair_card, symplectic_transverseTriple_card_lower, symplectic_transverseTriple_probability_lower, reduceSubspace_eq_bot_of_le, triplePairSum_split, triplePairSum_reduce_pair, triplePairSum_reductions_transverse, orderedTripleOrbit_lagrangians, avoidanceTripleReduction_uniform, avoidanceOrbitFiber_card_identity, avoidanceOrbitFiber_card_lower.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates08

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_10
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0127]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0136]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0193]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0196]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0205]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0210]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0212]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0215]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0228]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0229]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0231] :
  OAI.SidorenkoCounterexample.ProofCertificate_0232 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0233 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0234 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0235 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0236 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0237 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0238 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0239 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0240 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0241 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0242 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0243 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0244 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0245 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0246 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0247 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0248 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0249 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0250 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0251 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0252 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0253 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0254 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0255 := by sorry
