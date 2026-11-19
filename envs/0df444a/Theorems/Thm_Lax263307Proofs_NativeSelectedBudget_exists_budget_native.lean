-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSelectedBudget_exists_budget_native
-- name    : Lax263307Proofs.NativeSelectedBudget.exists_budget_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:27.205855+00:00
-- url     : https://prove2.me/theorems/784576fb-8e1e-45ef-9dd2-f6d569646433
-- title:
--   One polynomial budget for selected native backends
-- statement:
--   Fix a native core configuration, a selected LP program, a selected separator-call program and the rounded-update coefficient. The complete native demand function, including their width, time and storage allowances, is bounded by one natural polynomial envelope. Positive constants are chosen before every resource argument:
--
--   $$\exists Q,e>0\ \forall R\in\mathbb N,\quad\operatorname{demand}(R)\le Q(R+1)^e.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedBudget.lean, theorem exists_budget (lines 67–70)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeSelectedBudget
end Lax263307Proofs.NativeSelectedBudget

theorem Lax263307Proofs.NativeSelectedBudget.exists_budget_native : ∀ {lp flow : List Nat → List Nat} (cfg : Lax263307Proofs.NativeCoreMachine.Config)
  (p : Lax263307Proofs.NativeSelectedLP.Program lp) (q : Lax263307Proofs.NativeSelectedNear.Program flow) (c : Nat),
  ∃ (Q : Nat) (e : Nat),
    And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Q)
      (And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) e)
        (∀ (R : Nat),
          @LE.le Nat instLENat (@Lax263307Proofs.NativeSelectedBudget.demand lp flow cfg p q c R)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) Q
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                e)))) := by sorry
