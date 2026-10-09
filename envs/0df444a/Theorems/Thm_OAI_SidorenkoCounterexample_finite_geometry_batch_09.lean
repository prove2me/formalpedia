-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_09
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_09
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T05:57:37.914323+00:00
-- url     : https://prove2.me/theorems/089bb789-138a-4eba-9924-8c10227fbe9e
-- title:
--   Sidorenko construction: Orbits, SubspaceCounts, batch 09
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Orbits.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/SubspaceCounts.lean; source propositions orderedTripleOrbit_pair_injection, transverse_to_card, orderedTransversePair_card, orderedTransverseTriple_card_lower, symplecticLagrangian_card_bounds, symplecticLagrangian_card_pos, isotropic_finrank_le_half, containingLagrangian_card_bounds, isotropic_incidence_card, isotropicExponent_add, isotropic_card_bounds, lagrangianConstant_mono, lagrangian_bad_intersection_card, lagrangian_bad_intersection_scaled, lagrangian_disjoint_card_lower, reduceSubspace_isotropic, avoidance_card_lower, triple_containing_isometry_lift, submodule_map_trans, submodule_map_symm_cancel, pairLinearStabilizerRestriction_bijective, pairLinearOrbit_card_identity.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates07

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_09
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0010]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0013]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0015]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0038]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0069]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0114]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0117]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0118]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0120]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0127]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0131]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0133]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0134]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0143]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0144]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0145]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0205]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0208]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0209] :
  OAI.SidorenkoCounterexample.ProofCertificate_0210 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0211 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0212 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0213 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0214 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0215 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0216 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0217 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0218 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0219 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0220 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0221 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0222 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0223 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0224 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0225 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0226 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0227 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0228 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0229 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0230 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0231 := by sorry
