-- Prove2me | Theorems.Thm_Lax455465Proofs_RamProductAlgorithm_exists_polynomial_time_flow_cut
-- name    : Lax455465Proofs.RamProductAlgorithm.exists_polynomial_time_flow_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:17:00.48657+00:00
-- url     : https://prove2.me/theorems/de7ec77e-1ed6-40b9-a7c0-5609ff1407a3
-- title:
--   One polynomial-time RAM algorithm for the flow-cut alternative
-- statement:
--   There are a single polynomial-time word-RAM algorithm $f$ and a positive universal constant $C$ such that every valid rational product-demand network with at least two positive-demand vertices has a joint flow-cut certificate:
--   $$f(\operatorname{encode}(I))=\operatorname{encode}(\mathcal K),\qquad
--   \operatorname{IsValid}(\text{kind},I,C,\mathcal K).$$
--   The statement includes both edge models and total resource bounds on arbitrary input words.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamProductAlgorithm.lean, theorem exists_polynomial_time_flow_cut

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax455465Proofs.RamProductAlgorithm.exists_polynomial_time_flow_cut : ∃ (solve : List ℕ → List ℕ) (C : ℝ),
  Lax759944.RamPolytime.RamPolytime solve ∧
    0 < C ∧
      ∀ (kind : Lax455465.ProductNetwork.EdgeKind) (n : ℕ) (I : Lax455465.RationalEncoding.RationalInstance n),
        (kind = Lax455465.ProductNetwork.EdgeKind.undirected → I.network.IsUndirected) →
          2 ≤ Lax455465.ProductNetwork.supportCount I.weights →
            ∃ (certificate : Lax455465.FlowCutCertificate.Certificate n),
              solve (Lax455465.RationalEncoding.encodeInput kind I) =
                  Lax455465.FlowCutCertificate.encodeCertificate certificate ∧
                Lax455465.FlowCutCertificate.IsValid kind I C certificate := by sorry
