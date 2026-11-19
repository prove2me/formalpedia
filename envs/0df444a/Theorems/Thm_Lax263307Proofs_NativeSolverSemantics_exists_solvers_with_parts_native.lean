-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSolverSemantics_exists_solvers_with_parts_native
-- name    : Lax263307Proofs.NativeSolverSemantics.exists_solvers_with_parts_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:30.877297+00:00
-- url     : https://prove2.me/theorems/f867507f-8485-4dba-b93c-be774a5bc668
-- title:
--   Uniform backend choices and weighted algorithm correctness
-- statement:
--   Let $\mathcal C$ be hereditary with strongly edge-sublinear separators. There are fixed polynomial word-RAM LP and flow functions and positive integer structural parameters. The LP function satisfies the exact certificate-reader contract; the flow and recursive oracle contracts hold on the independent blow-up class. For every $G\in\mathcal C$, rational weight vector $w$ and $0<\varepsilon<1$, the same selected functions satisfy
--
--   $$w(\operatorname{solve}(G,w,\varepsilon))\ge(1-\varepsilon)\alpha_w(G).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSolverSemantics.lean, theorem exists_solvers_with_parts (lines 15–54)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeSolverSemantics
end Lax263307Proofs.NativeSolverSemantics

theorem Lax263307Proofs.NativeSolverSemantics.exists_solvers_with_parts_native : ∀ (C : Lax263307.GraphClasses.GraphClass),
  Lax263307.GraphClasses.IsHereditary C →
    Lax263307.EdgeSublinearSeparators.HasStronglyEdgeSublinearSeparators C →
      ∃ (lp : List Nat → List Nat) (flow : List Nat → List Nat) (a : Nat) (A : Nat) (K : Nat) (b : Nat),
        And (Lax759944.RamPolytime.RamPolytime lp)
          (And (Lax263307Proofs.NativeEncodedLP.Encoded lp)
            (And (Lax759944.RamPolytime.RamPolytime flow)
              (And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a)
                (And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) A)
                  (And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) K)
                    (And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
                      (And (Lax263307.PowerBagBounds.HasPowerBagBound (Lax263307.BlowUpClasses.blowUpClass C) a A)
                        (And
                          (Lax263307Proofs.NearOracle.SeparatorCorrect (Lax263307.BlowUpClasses.blowUpClass C) flow a K
                            b)
                          (And
                            (Lax263307Proofs.NativeRecursiveOracle.OracleCorrect (Lax263307.BlowUpClasses.blowUpClass C)
                              lp flow a K b)
                            (∀ (n : Nat) (G : SimpleGraph (Fin n))
                              [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
                              @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n)))
                                  (@Set.instMembership (SimpleGraph (Fin n))) (C n) G →
                                ∀ (weights : Fin n → Rat) (ε : Rat),
                                  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε →
                                    @LT.lt Rat Rat.instLT ε
                                        (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) →
                                      @Lax263307.WeightedIndependentSet.IsApproximation n G weights ε
                                        (@Lax263307.WeightedAlgorithm.solve n lp flow a K b G inst weights ε))))))))))) := by sorry
