-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_12
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_12
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:18:34.423212+00:00
-- url     : https://prove2.me/theorems/53fe2688-c588-4d80-8b2f-8bd4e667bf00
-- title:
--   Sidorenko construction: OrbitBounds, batch 12
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/OrbitBounds.lean; source propositions reduceSubspace_finrank_containing, commonOrbit_injection, commonOrbit_card_lower, pairOrbitConstant_mono, orbitMassConstant_pos, tripleOrbit_card_lower, triple_subspace_orbit_surjection, triple_subspace_orbit_card_identity, subspace_map_eq_of_restriction_equiv, triple_decomposition_equiv, triple_comap_isCompl, triple_isotropic_config_transitivity, triple_isotropic_orbit_card_upper, commonZeroProfile_injection, profileMassConstant_pos, profileMassConstant_mono, commonZeroProfile_card_upper, reducePair_finrank, reduceLagrangian_injective.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_12
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0112]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0114]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0117]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0118]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0119]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0120]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0121]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0139]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0144]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0145]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0168]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0169]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0217]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0220]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0221]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0227]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0228]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0229]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0238]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0242]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0252]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0257]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_0262]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_0263]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_0264]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_0265]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_0270]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_0271]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_0272]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_0273]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_0275]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_0276] :
  OAI.SidorenkoCounterexample.ProofCertificate_0277 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0278 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0279 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0280 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0281 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0282 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0283 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0284 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0285 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0286 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0287 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0288 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0289 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0290 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0291 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0292 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0293 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0294 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0295 := by sorry
