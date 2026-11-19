-- Prove2me | Theorems.Thm_Lax455465Proofs_RamOutputResources_command_spec_native
-- name    : Lax455465Proofs.RamOutputResources.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:44.459714+00:00
-- url     : https://prove2.me/theorems/0312903b-b0f0-4e47-b7f8-f429adcf8bf7
-- title:
--   Polynomial native serialization of a cut and converted primal flow
-- statement:
--   Fix a rational network instance $I$, a cut $S$, and a componentwise nonnegative primal vector $z$ whose height is bounded by $2^{P(L)}$. Under the stated polynomial word budget and initialized conversion/output buffers, the fixed writer returns exactly the joint encoding of $S$ and the converted primal flow:
--
--   $$\mathrm{output}=\operatorname{encodeCertificate}(S,\operatorname{convertFlow}(z)).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamOutputResources.lean, theorem command_spec (lines 52–68)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax455465Proofs.RamOutputResources
end Lax455465Proofs.RamOutputResources

theorem Lax455465Proofs.RamOutputResources.command_spec_native : ∀ (P : @Polynomial Nat Nat.instSemiring) {n : Nat} (kind : Lax455465.ProductNetwork.EdgeKind)
  (I : Lax455465.RationalEncoding.RationalInstance n) (S : Finset (Fin n))
  (z :
    Fin
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))) →
      Rat)
  (hz :
    ∀
      (i :
        Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))),
      @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (z i)),
  (∀
      (i :
        Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))),
      Lax455465Proofs.LpInputSize.Height
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) P))
        (z i)) →
    ∀ (W : Nat),
      @LE.le Nat instLENat
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
            (Lax455465Proofs.RamOutputResources.wordBound P))
          W →
        Lax808846Proofs.Reasoning.Spec
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)
          (fun (σ : Lax808846Proofs.Imp.Env) =>
            And
              (Lax455465Proofs.RamFlowConvert.Context kind
                (@Lax455465Proofs.RamOptimalDecode.vector
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)))
                  z hz)
                σ)
              (And (@Eq Nat (σ.vars "metric.n") n)
                (And
                  (Lax455465Proofs.RamVirtualState.Prefix
                    (Lax455465Proofs.RamUnsignedBuffer.encode (@Lax455465Proofs.CutScoreData.vertexFlags n S))
                    "cut.flags" σ)
                  (And
                    (@LT.lt Nat instLTNat
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))))
                      (@List.length Nat (σ.arrs "flow.converted")))
                    (@Eq (List Nat) σ.out (@List.nil Nat))))))
          Lax455465Proofs.RamJointOutput.command
          (fun (x τ : Lax808846Proofs.Imp.Env) =>
            @Eq (List Nat) τ.out
              (@Lax455465.FlowCutCertificate.encodeCertificate n
                (@Lax455465.FlowCutCertificate.Certificate.mk n S
                  (@Lax455465Proofs.CertificatePostprocessing.convertFlow n kind
                    (@Lax455465Proofs.CertificatePostprocessing.primalFlow n z)))))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
            (Lax455465Proofs.RamOutputResources.timeBound P)) := by sorry
