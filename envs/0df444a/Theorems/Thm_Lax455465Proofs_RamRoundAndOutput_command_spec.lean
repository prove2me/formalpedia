-- Prove2me | Theorems.Thm_Lax455465Proofs_RamRoundAndOutput_command_spec
-- name    : Lax455465Proofs.RamRoundAndOutput.command_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:00.423335+00:00
-- url     : https://prove2.me/theorems/aa05a180-cbd7-4d51-aaa0-c93eda7ba1ee
-- title:
--   Bounded native metric rounding and flow-cut output
-- statement:
--   Given a rational product-demand instance, matching primal and dual feasible solutions, and its certified rational distance metric, assume the specified height, workspace and host-width bounds. The fixed rounding-and-output command returns a joint flow-cut certificate with approximation constant $512$ within its polynomial time bound:
--   $$\operatorname{IsValid}(\text{kind},I,512,\mathcal K).$$
--   Both directed and undirected edge models are included.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRoundAndOutput.lean, theorem command_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax455465Proofs.RamRoundAndOutput.command_spec : ∀ (metric primal : Polynomial ℕ) {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind)
  (I : Lax455465.RationalEncoding.RationalInstance n) (z : Fin (1 + n * n * (n * n)) → ℚ)
  (y : Fin (n * n + 2 * (n * n * n)) → ℚ)
  (hz : Lax109476.LinearProgram.PrimalFeasible (Lax455465Proofs.DirectedFlowLP.program I) z),
  Lax109476.LinearProgram.DualFeasible (Lax455465Proofs.DirectedFlowLP.program I) y →
    Lax109476.LinearProgram.primalValue (Lax455465Proofs.DirectedFlowLP.program I) z =
        Lax109476.LinearProgram.dualValue (Lax455465Proofs.DirectedFlowLP.program I) y →
      ∀ (d : Lax455465Proofs.MetricMatrix.Matrix n),
        Lax455465Proofs.MetricMatrix.rational d = Lax455465Proofs.RationalDistances.dualDistance y →
          (∀ (u v : Fin n),
              Lax455465Proofs.LpInputSize.Height
                (2 ^
                  Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                    metric)
                ↑(d u v)) →
            (∀ (i : Fin (1 + n * n * (n * n))),
                Lax455465Proofs.LpInputSize.Height
                  (2 ^
                    Polynomial.eval
                      (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I)) primal)
                  (z i)) →
              2 ≤ Lax455465.ProductNetwork.supportCount I.weights →
                (kind = Lax455465.ProductNetwork.EdgeKind.undirected → I.network.IsUndirected) →
                  ∀ (W : ℕ),
                    Polynomial.eval
                          (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                          (Lax455465Proofs.RamRoundAndOutput.wordBound metric primal) ≤
                        W →
                      Lax808846Proofs.Reasoning.Spec (2 ^ W)
                        (fun (σ : Lax808846Proofs.Imp.Env) =>
                          Lax455465Proofs.RamMetricRounding.Input I d σ ∧
                            Lax455465Proofs.RamRegionInvariant.Room n (Lax455465Proofs.RamRoundingInit.support I.weight)
                                σ ∧
                              Lax455465Proofs.RamRegionCut.Room n σ ∧
                                Lax455465Proofs.RamFlowConvert.Context kind
                                    (Lax455465Proofs.RamOptimalDecode.vector z hz.1) σ ∧
                                  2 * (1 + n * n * (n * n)) < (σ.arrs "flow.converted").length ∧ σ.out = [])
                        Lax455465Proofs.RamRoundAndOutput.command
                        (fun (x τ : Lax808846Proofs.Imp.Env) =>
                          ∃ (certificate : Lax455465.FlowCutCertificate.Certificate n),
                            Lax455465.FlowCutCertificate.IsValid kind I 512 certificate ∧
                              τ.out = Lax455465.FlowCutCertificate.encodeCertificate certificate)
                        (Polynomial.eval
                          (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                          (Lax455465Proofs.RamRoundAndOutput.timeBound metric primal)) := by sorry
