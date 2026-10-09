-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_finite_geometry_batch_20
-- name    : OAI.SidorenkoCounterexample.finite_geometry_batch_20
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T06:12:42.782307+00:00
-- url     : https://prove2.me/theorems/0124e035-d766-42fa-a9d3-998c32501636
-- title:
--   Sidorenko construction: Spans, Tail, batch 20
-- statement:
--   Let $P_j$ be the fully quantified source propositions named below, specialized to carriers in Type. For the earlier propositions $I$ and the new propositions $B$ listed in the formal statement, this result establishes
--   $$\left(\bigwedge_{j\in I}P_j\right)\Longrightarrow\bigwedge_{k\in B}P_k.$$
--   Every source hypothesis and quantifier is retained. The conclusions supply the next geometry, counting, or moment identities in the finite kernel construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Spans.lean; https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Tail.lean; source propositions directPairProfileCoding_injective, familyContainment_card_bound, directPairProfile_card_bound, pairSpanStratumCoding_injective, localFamilyStratum_card_bound, familySpan_exponent_cast, pairSpanStratum_card_bound, residual_h_sum_le, pairProfile_global_dim_le, pairProfile_local_dim_le, nondirectFiberInjection_injective, pairStratum_residual_bound, nondirectFiber_card_bound, nondirectPairProfile_card_bound, fullTailConstant_nonneg, fullTailMajorant_nonneg, fullTailMajorant_eq, tripleFaceDensity_tail_bound, lowerTailTuple_s, lowerTailTuple_feasible, lowerTailConstant_pos, pairParameters_card_le, pairFaceDensity_lower_tail, faceTailConstant_pos, faceTailTuple_c, faceTailTuple_s, faceTailTuple_feasible, faceTailMajorant_true, faceTailMajorant_false, faceTailMajorant_nonneg, PointProfile.faceLocal, PointProfile.geometric, profileCost_baseline, globalTailConstant_nonneg, globalTailTuple_feasible, globalTailGain_cost, prod_faceTailMajorant.

import Mathlib
import Definitions.Def_SidorenkoCertificateBundleA

theorem OAI.SidorenkoCounterexample.finite_geometry_batch_20
  [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0207]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0216]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0281]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0334]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0351]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0352]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0356]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0407]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0411]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0412]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0413]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0414]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0436]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0437]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0439]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0458]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0468]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0492]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0494]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0498]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0506]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0508]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_0514]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_0517]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_0518]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_0522]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_0528]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_0531]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_0533]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_0534] :
  OAI.SidorenkoCounterexample.ProofCertificate_0535 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0536 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0537 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0538 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0539 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0540 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0541 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0542 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0543 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0544 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0545 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0546 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0547 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0548 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0549 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0550 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0551 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0552 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0553 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0554 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0555 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0556 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0557 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0558 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0559 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0560 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0561 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0562 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0563 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0564 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0565 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0566 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0567 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0568 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0569 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0570 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0571 := by sorry
