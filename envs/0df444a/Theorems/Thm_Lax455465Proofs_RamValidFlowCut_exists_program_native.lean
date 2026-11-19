-- Prove2me | Theorems.Thm_Lax455465Proofs_RamValidFlowCut_exists_program_native
-- name    : Lax455465Proofs.RamValidFlowCut.exists_program_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:28.466413+00:00
-- url     : https://prove2.me/theorems/4a2d9636-1574-460e-a99c-3495478d11c4
-- title:
--   A fixed native command for valid flow-or-cut input
-- statement:
--   There exist one fixed structured command and polynomial time, word-width and source-simulation bounds that work uniformly on valid encoded weighted flow instances. For an instance with at least two supported endpoints, and symmetric adjacency in the undirected case, sufficiently many word bits and the complete source, metric, region and output workspace, the command terminates with a valid factor-$512$ flow-or-cut certificate:
--   $$\operatorname{out}=\operatorname{encode}(\mathcal K),\qquad\operatorname{Valid}_{512}(\mathcal K).$$
--   Its instruction count is bounded by the fixed time polynomial evaluated at the binary size of the encoded input. The result includes actual execution and output encoding, for the given operational initialization.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamValidFlowCut.lean, theorem Lax455465Proofs.RamValidFlowCut.exists_program, line 15

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax455465Proofs.RamValidFlowCut
end Lax455465Proofs.RamValidFlowCut

theorem Lax455465Proofs.RamValidFlowCut.exists_program_native : ∃ (c : Lax808846Proofs.Imp.Com) (timeBound : @Polynomial Nat Nat.instSemiring) (wordBound :
  @Polynomial Nat Nat.instSemiring) (sourceTime : @Polynomial Nat Nat.instSemiring),
  ∀ {n : Nat} (kind : Lax455465.ProductNetwork.EdgeKind) (I : Lax455465.RationalEncoding.RationalInstance n),
    (@Eq Lax455465.ProductNetwork.EdgeKind kind Lax455465.ProductNetwork.EdgeKind.undirected →
        @Lax455465.ProductNetwork.Network.IsUndirected n (@Lax455465.RationalEncoding.RationalInstance.network n I)) →
      @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Lax455465.ProductNetwork.supportCount n (@Lax455465.RationalEncoding.RationalInstance.weights n I)) →
        ∀ (W : Nat),
          @LE.le Nat instLENat
              (@Polynomial.eval Nat Nat.instSemiring
                (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) wordBound)
              W →
            Lax808846Proofs.Reasoning.Spec
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
              (fun (σ : Lax808846Proofs.Imp.Env) =>
                And
                  (@Eq (List Nat) σ.inp
                    (@List.cons Nat (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (@Lax455465.RationalEncoding.encodeInput n kind I)))
                  (And
                    (@LE.le Nat instLENat (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (@List.length Nat (σ.arrs "input.data")))
                    (And
                      (@LT.lt Nat instLTNat
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                        (@List.length Nat (σ.arrs "flow.weights")))
                      (And
                        (@LT.lt Nat instLTNat
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                          (@List.length Nat (σ.arrs "flow.capacities")))
                        (And
                          (@LT.lt Nat instLTNat (Lax455465Proofs.RamFlowLp.wordLength n)
                            (@List.length Nat (σ.arrs "lp.word")))
                          (And
                            (@LT.lt Nat instLTNat
                              (@List.length Nat
                                (@Lax109476.RationalEncoding.encodeProgram
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
                                  (@Lax455465Proofs.DirectedFlowLP.program n I)))
                              (@List.length Nat (σ.arrs "vm.input")))
                            (And
                              (@LT.lt Nat instLTNat
                                (@Polynomial.eval Nat Nat.instSemiring
                                  (Lax759944.BinaryWordEncoding.bitSize
                                    (@Lax109476.RationalEncoding.encodeProgram
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
                                      (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                  sourceTime)
                                (@List.length Nat (σ.arrs "vm.addresses")))
                              (And
                                (@LT.lt Nat instLTNat
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (Lax759944.BinaryWordEncoding.bitSize
                                      (@Lax109476.RationalEncoding.encodeProgram
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
                                        (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                    sourceTime)
                                  (@List.length Nat (σ.arrs "vm.values")))
                                (And
                                  (@LT.lt Nat instLTNat
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (Lax759944.BinaryWordEncoding.bitSize
                                        (@Lax109476.RationalEncoding.encodeProgram
                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))
                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
                                          (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                      sourceTime)
                                    (@List.length Nat (σ.arrs "vm.output")))
                                  (And
                                    (@LT.lt Nat instLTNat
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (Lax455465Proofs.RamFlowData.columns n))
                                      (@List.length Nat (σ.arrs "flow.primal")))
                                    (And
                                      (@LT.lt Nat instLTNat
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (Lax455465Proofs.RamFlowData.rows n))
                                        (@List.length Nat (σ.arrs "flow.dual")))
                                      (And
                                        (@LT.lt Nat instLTNat
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                          (@List.length Nat (σ.arrs "metric.old")))
                                        (And
                                          (@LT.lt Nat instLTNat
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                            (@List.length Nat (σ.arrs "metric.new")))
                                          (And
                                            (Lax455465Proofs.RamRegionInvariant.Room n
                                              (@Lax455465Proofs.RamRoundingInit.support n
                                                (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                              σ)
                                            (And (Lax455465Proofs.RamRegionCut.Room n σ)
                                              (And
                                                (@LT.lt Nat instLTNat
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    (Lax455465Proofs.RamFlowData.columns n))
                                                  (@List.length Nat (σ.arrs "flow.converted")))
                                                (@Eq (List Nat) σ.out (@List.nil Nat))))))))))))))))))
              c
              (fun (x τ : Lax808846Proofs.Imp.Env) =>
                ∃ (certificate : Lax455465.FlowCutCertificate.Certificate n),
                  And
                    (@Lax455465.FlowCutCertificate.IsValid n kind I
                      (@OfNat.ofNat Real (nat_lit 512)
                        (@instOfNatAtLeastTwo Real (nat_lit 512) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
                      certificate)
                    (@Eq (List Nat) τ.out (@Lax455465.FlowCutCertificate.encodeCertificate n certificate)))
              (@Polynomial.eval Nat Nat.instSemiring
                (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) timeBound) := by sorry
