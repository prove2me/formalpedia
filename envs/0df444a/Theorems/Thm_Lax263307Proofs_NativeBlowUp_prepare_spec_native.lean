-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeBlowUp_prepare_spec_native
-- name    : Lax263307Proofs.NativeBlowUp.prepare_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:10.031891+00:00
-- url     : https://prove2.me/theorems/fd99bf8f-2a02-4f46-98e9-f8edfd89e9f4
-- title:
--   Bounded construction of the rounded independent blow-up
-- statement:
--   Let $G$ be a graph on $n$ labelled vertices, $w$ rational signed vertex weights and $\varepsilon>0$ rational. Suppose their numerator and denominator magnitudes are bounded by $M\ge1$, with $n\le M$, and the published arithmetic, dimension and buffer guards hold for word bound $B$. Put $c_v=\operatorname{copies}(\max(w,0),\varepsilon)_v$ and $N=\sum_v c_v$. From the encoded input, the fixed preparation command stores the independent blow-up adjacency matrix, its owner map, its order and the original input tail:
--   $$\operatorname{matrix}_{\rm out}=\operatorname{Adj}(G[c]),\qquad\operatorname{owner}_{\rm out}=\operatorname{owners}(c),\qquad n_{\rm out}=N.$$
--   Its instruction bound is the source's explicit $\operatorname{cost}(n,N)$; it preserves prior output and the original graph order. This is the operational bridge from signed weighted input to an unweighted graph.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeBlowUp.lean, theorem Lax263307Proofs.NativeBlowUp.prepare_spec, line 459

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax263307Proofs.NativeBlowUp
end Lax263307Proofs.NativeBlowUp

theorem Lax263307Proofs.NativeBlowUp.prepare_spec_native : ∀ {n : Nat} (B M : Nat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LE.le Nat instLENat n M →
      ∀ (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (w : Fin n → Rat)
        (ε : Rat),
        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε →
          (∀ (v : Fin n), And (@LE.le Nat instLENat (w v).num.natAbs M) (@LE.le Nat instLENat (w v).den M)) →
            And (@LE.le Nat instLENat ε.num.natAbs M) (@LE.le Nat instLENat ε.den M) →
              @LT.lt Nat instLTNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        M (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                    (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  B →
                @LT.lt Nat instLTNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    B →
                  @LT.lt Nat instLTNat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                (∑ v : Fin n,
                                  @Lax263307.WeightRounding.copies n
                                    (fun (v : Fin n) =>
                                      @Max.max Rat Rat.instSup (w v)
                                        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
                                    ε v)
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            n)
                          (∑ v : Fin n,
                            @Lax263307.WeightRounding.copies n
                              (fun (v : Fin n) =>
                                @Max.max Rat Rat.instSup (w v)
                                  (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
                              ε v))
                        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      B →
                    have cs :=
                      @Lax263307.WeightRounding.copies n
                        (fun (v : Fin n) =>
                          @Max.max Rat Rat.instSup (w v) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
                        ε;
                    have N := ∑ v : Fin n, cs v;
                    Lax808846Proofs.Reasoning.Spec B
                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                        And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst w ε))
                          (And
                            (@LE.le Nat instLENat
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                    (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
                                (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@List.length Nat (σ.arrs "input.data")))
                            (And (@LE.le Nat instLENat n (@List.length Nat (σ.arrs "copy.counts")))
                              (And (@LE.le Nat instLENat N (@List.length Nat (σ.arrs "blowup.owner")))
                                (@LE.le Nat instLENat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) N N)
                                  (@List.length Nat (σ.arrs "blowup.matrix")))))))
                      Lax263307Proofs.NativeBlowUp.prepare
                      (fun (σ τ : Lax808846Proofs.Imp.Env) =>
                        And
                          (Lax455465Proofs.RamVirtualState.Prefix
                            (@Lax263307Proofs.NativeBlowUp.numberedMatrix n G inst cs) "blowup.matrix" τ)
                          (And
                            (Lax455465Proofs.RamVirtualState.Prefix (@Lax263307Proofs.NativeBlowUp.owners n cs)
                              "blowup.owner" τ)
                            (And (@Eq Nat (τ.vars "blowup.length") N)
                              (And
                                (Lax455465Proofs.RamVirtualState.Prefix
                                  (@Lax263307Proofs.NativeFrontend.tailInput n G inst w ε) "input.data" τ)
                                (And (@Eq (List Nat) τ.out σ.out) (@Eq Nat (τ.vars "input.n") n))))))
                      (Lax263307Proofs.NativeBlowUp.cost n N) := by sorry
