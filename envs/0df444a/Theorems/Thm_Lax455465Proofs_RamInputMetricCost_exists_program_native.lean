-- Prove2me | Theorems.Thm_Lax455465Proofs_RamInputMetricCost_exists_program_native
-- name    : Lax455465Proofs.RamInputMetricCost.exists_program_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:37.33854+00:00
-- url     : https://prove2.me/theorems/242b643d-7af3-4f58-b8b2-6a6675f0ff62
-- title:
--   Compute matching flow-LP witnesses and their exact metric cost
-- statement:
--   There exist a fixed native command and fixed polynomial time, word-width, source-time and source-word bounds, uniform over encoded rational flow instances with at least two supported endpoints. From the complete source input and virtual-machine workspace, the command obtains rational primal and dual feasible witnesses $z,y$ with
--   $$\operatorname{primalValue}(z)=\operatorname{dualValue}(y),$$
--   and stores the exact dual-distance metric and its metric cost. The optimal certificate fits the stated source-word bound, and the command writes no output and runs within its fixed time polynomial. These witness, storage and resource conclusions hold simultaneously for every sufficiently large host width.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamInputMetricCost.lean, theorem Lax455465Proofs.RamInputMetricCost.exists_program, line 15

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax455465Proofs.RamInputMetricCost
end Lax455465Proofs.RamInputMetricCost

theorem Lax455465Proofs.RamInputMetricCost.exists_program_native : ∃ (c : Lax808846Proofs.Imp.Com) (timeBound : @Polynomial Nat Nat.instSemiring) (wordBound :
  @Polynomial Nat Nat.instSemiring) (sourceTime : @Polynomial Nat Nat.instSemiring) (sourceWord :
  @Polynomial Nat Nat.instSemiring),
  And c.NoWrite
    (∀ {n : Nat} (kind : Lax455465.ProductNetwork.EdgeKind) (I : Lax455465.RationalEncoding.RationalInstance n),
      @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Lax455465.ProductNetwork.supportCount n (@Lax455465.RationalEncoding.RationalInstance.weights n I)) →
        ∃ (z : Fin (Lax455465Proofs.RamFlowData.columns n) → Rat) (y : Fin (Lax455465Proofs.RamFlowData.rows n) → Rat)
          (hz :
          @Lax109476.LinearProgram.PrimalFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
            Rat.instPartialOrder
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) z)
          (hy :
          @Lax109476.LinearProgram.DualFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.instPartialOrder
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) y),
          And
            (@Eq Rat
              (@Lax109476.LinearProgram.primalValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                (@Lax455465Proofs.DirectedFlowLP.program n I) z)
              (@Lax109476.LinearProgram.dualValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                (@Lax455465Proofs.DirectedFlowLP.program n I) y))
            (And
              (Lax759944.RamPolytime.FitsInWords
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
                  sourceWord)
                (@Lax109476.RationalEncoding.encodeCertificate (Lax455465Proofs.RamFlowData.rows n)
                  (Lax455465Proofs.RamFlowData.columns n)
                  (@Lax109476.RationalCertificates.Certificate.optimal (Lax455465Proofs.RamFlowData.rows n)
                    (Lax455465Proofs.RamFlowData.columns n) z y)))
              (∀ (W : Nat),
                @LE.le Nat instLENat
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      wordBound)
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
                                              (@LT.lt Nat instLTNat
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                                (@List.length Nat (σ.arrs "metric.new")))))))))))))))
                    c
                    (fun (x τ : Lax808846Proofs.Imp.Env) =>
                      And (@Lax455465Proofs.RamFlowData.Data n I τ)
                        (And (@Eq Nat (τ.vars "metric.n") n)
                          (And (@Eq Nat (τ.vars "metric.n2") (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                            (And (@Eq Nat (τ.vars "flow.kind") (Lax455465Proofs.RamGraphHeader.tag kind))
                              (And
                                (Lax455465Proofs.RamVirtualState.Prefix
                                  (Lax455465Proofs.RamUnsignedBuffer.encode
                                    (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.columns n) z
                                      (@And.left
                                        (∀
                                          (j :
                                            Fin
                                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))),
                                          @LE.le Rat
                                            (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                            (@OfNat.ofNat Rat (nat_lit 0)
                                              (@Zero.toOfNat0 Rat
                                                (@MulZeroClass.toZero Rat
                                                  (@instMulZeroClassOfSemiring Rat
                                                    (@Ring.toSemiring Rat
                                                      (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                            (z j))
                                        (∀
                                          (i :
                                            Fin
                                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))),
                                          @LE.le Rat
                                            (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                            (@Lax109476.LinearProgram.rowValue Rat
                                              (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                              (@Lax455465Proofs.DirectedFlowLP.program n I) z i)
                                            (@Lax109476.LinearProgram.Program.b Rat
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
                                              (@Lax455465Proofs.DirectedFlowLP.program n I) i))
                                        hz)))
                                  "flow.primal" τ)
                                (And
                                  (Lax455465Proofs.RamVirtualState.Prefix
                                    (Lax455465Proofs.RamUnsignedBuffer.encode
                                      (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.rows n) y
                                        (@And.left
                                          (∀
                                            (i :
                                              Fin
                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))),
                                            @LE.le Rat
                                              (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                              (@OfNat.ofNat Rat (nat_lit 0)
                                                (@Zero.toOfNat0 Rat
                                                  (@MulZeroClass.toZero Rat
                                                    (@instMulZeroClassOfSemiring Rat
                                                      (@Ring.toSemiring Rat
                                                        (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                              (y i))
                                          (∀
                                            (j :
                                              Fin
                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))),
                                            @LE.le Rat
                                              (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                              (@Lax109476.LinearProgram.Program.c Rat
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
                                                (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                              (@Lax109476.LinearProgram.columnValue Rat
                                                (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                                (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                          hy)))
                                    "flow.dual" τ)
                                  (And
                                    (Lax455465Proofs.RamVirtualState.Prefix
                                      (Lax455465Proofs.RamUnsignedBuffer.encode
                                        (@Lax455465Proofs.MetricMatrix.values n
                                          (@Lax455465Proofs.RamDualDistances.result n y
                                            (@And.left
                                              (∀
                                                (i :
                                                  Fin
                                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))),
                                                @LE.le Rat
                                                  (@Preorder.toLE Rat
                                                    (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                  (@OfNat.ofNat Rat (nat_lit 0)
                                                    (@Zero.toOfNat0 Rat
                                                      (@MulZeroClass.toZero Rat
                                                        (@instMulZeroClassOfSemiring Rat
                                                          (@Ring.toSemiring Rat
                                                            (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                                  (y i))
                                              (∀
                                                (j :
                                                  Fin
                                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))),
                                                @LE.le Rat
                                                  (@Preorder.toLE Rat
                                                    (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                  (@Lax109476.LinearProgram.Program.c Rat
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
                                                    (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                                  (@Lax109476.LinearProgram.columnValue Rat
                                                    (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                                    (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                              hy))))
                                      "metric.old" τ)
                                    (Lax455465Proofs.RamUnsignedScalar.Stored "round.cost"
                                      (@Lax455465Proofs.MetricCostData.cost n I
                                        (@Lax455465Proofs.RamDualDistances.result n y
                                          (@And.left
                                            (∀
                                              (i :
                                                Fin
                                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) n)))),
                                              @LE.le Rat
                                                (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                (@OfNat.ofNat Rat (nat_lit 0)
                                                  (@Zero.toOfNat0 Rat
                                                    (@MulZeroClass.toZero Rat
                                                      (@instMulZeroClassOfSemiring Rat
                                                        (@Ring.toSemiring Rat
                                                          (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                                (y i))
                                            (∀
                                              (j :
                                                Fin
                                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))),
                                              @LE.le Rat
                                                (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                                (@Lax109476.LinearProgram.Program.c Rat
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
                                                  (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                                (@Lax109476.LinearProgram.columnValue Rat
                                                  (@DivisionRing.toRing Rat Rat.instDivisionRing)
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
                                                  (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                            hy)))
                                      τ))))))))
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      timeBound)))) := by sorry
