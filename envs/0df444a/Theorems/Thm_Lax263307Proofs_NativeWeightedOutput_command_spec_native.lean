-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeWeightedOutput_command_spec_native
-- name    : Lax263307Proofs.NativeWeightedOutput.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:11.663114+00:00
-- url     : https://prove2.me/theorems/8060a3d2-e077-41b5-8d13-6475a7ac8dc9
-- title:
--   Project a native blow-up answer to its original membership mask
-- statement:
--   Let $c_v$ be natural copy counts on $n$ vertices, let $N=\sum_v c_v$, and let $I$ be any subset of the $N$ numbered copies. Assume $n+N+5<B$ and $2^N<B$, a stored owner table, the mask of $I$, and the stated output-buffer lengths. The fixed command appends precisely the original-vertex membership encoding of the projection of $I$:
--   $$\operatorname{out}_{\rm final}=\operatorname{out}_{\rm initial}\mathbin{+\!+}\operatorname{encode}\{\operatorname{owner}(u):u\in I\}.$$
--   It uses at most $24n+44N+36$ instructions. This output contract applies to every subset of copies, independently of any later independence or approximation argument.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeWeightedOutput.lean, theorem Lax263307Proofs.NativeWeightedOutput.command_spec, line 44

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax263307Proofs.NativeWeightedOutput
end Lax263307Proofs.NativeWeightedOutput

theorem Lax263307Proofs.NativeWeightedOutput.command_spec_native : ∀ {n : Nat} (B : Nat) (copies : Fin n → Nat) (I : Finset (Fin (∑ v : Fin n, copies v))),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (∑ v : Fin n, copies v))
        (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      B →
    @LT.lt Nat instLTNat
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (∑ v : Fin n, copies v))
        B →
      Lax808846Proofs.Reasoning.Spec B
        (fun (σ : Lax808846Proofs.Imp.Env) =>
          And (@Eq Nat (σ.vars "input.n") n)
            (And (@Eq Nat (σ.vars "blowup.length") (∑ v : Fin n, copies v))
              (And (@Eq Nat (σ.vars "root.mask") (@Lax263307Proofs.NativeMasks.mask (∑ v : Fin n, copies v) I))
                (And
                  (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeBlowUp.owners n copies) "blowup.owner"
                    σ)
                  (And (@LE.le Nat instLENat (∑ v : Fin n, copies v) (@List.length Nat (σ.arrs "image.labels")))
                    (@Eq Nat (@List.length Nat (σ.arrs "image.output")) n))))))
        Lax263307Proofs.NativeWeightedOutput.command
        (fun (σ τ : Lax808846Proofs.Imp.Env) =>
          @Eq (List Nat) τ.out
            (@HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat))
              σ.out
              (@Lax263307.IndependentSetEncoding.encodeOutput n
                (@Lax263307.IndependentBlowUp.project n copies
                  (@Finset.image (Fin (∑ v : Fin n, copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies)
                    (fun (a b : @Lax263307.IndependentBlowUp.Vertex n copies) =>
                      @Sigma.instDecidableEqSigma (Fin n) (fun (v : Fin n) => Fin (copies v)) (instDecidableEqFin n)
                        (fun (a : Fin n) => instDecidableEqFin (copies a)) a b)
                    (@DFunLike.coe (Equiv (Fin (∑ v : Fin n, copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies))
                      (Fin (∑ v : Fin n, copies v))
                      (fun (x : Fin (∑ v : Fin n, copies v)) => @Lax263307.IndependentBlowUp.Vertex n copies)
                      (@EquivLike.toFunLike
                        (Equiv (Fin (∑ v : Fin n, copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies))
                        (Fin (∑ v : Fin n, copies v)) (@Lax263307.IndependentBlowUp.Vertex n copies)
                        (@Equiv.instEquivLike (Fin (∑ v : Fin n, copies v))
                          (@Lax263307.IndependentBlowUp.Vertex n copies)))
                      (@Lax263307.WeightedAlgorithm.labeling n copies))
                    I)))))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
              (@OfNat.ofNat Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) n)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
              (@OfNat.ofNat Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) (∑ v : Fin n, copies v)))
          (@OfNat.ofNat Nat (nat_lit 36) (instOfNatNat (nat_lit 36)))) := by sorry
