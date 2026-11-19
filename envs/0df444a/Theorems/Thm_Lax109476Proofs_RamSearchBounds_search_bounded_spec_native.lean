-- Prove2me | Theorems.Thm_Lax109476Proofs_RamSearchBounds_search_bounded_spec_native
-- name    : Lax109476Proofs.RamSearchBounds.search_bounded_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:06.963046+00:00
-- url     : https://prove2.me/theorems/76074027-60a2-4efa-ba29-d16fd650e8f2
-- title:
--   Uniform bounded execution of exact ellipsoid search
-- statement:
--   Let $A$ be an integer $m\times n$ matrix with $n\ge2$, let $b$ be rational, and let $N$ be a search budget. Suppose matrix magnitudes and right-hand-side heights are bounded by $2^\ell$, and the host width meets the explicit search bound. From the complete stored rows, right-hand side and ellipsoid workspace, the fixed search command runs within $T(m,n,N,\ell)$ instructions and returns the exact first successful trajectory index:
--   $$\operatorname{findFirst}(0,N)=\begin{cases}\operatorname{some}(j)&\text{if the output flag is }1,\\\operatorname{none}&\text{otherwise}.\end{cases}$$
--   Success means the rational trajectory point has no violated row. The full search invariant is retained, without assuming the existence of a feasible point.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSearchBounds.lean, theorem Lax109476Proofs.RamSearchBounds.search_bounded_spec, line 65

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax109476Proofs.RamSearchBounds
end Lax109476Proofs.RamSearchBounds

theorem Lax109476Proofs.RamSearchBounds.search_bounded_spec_native : ∀ {m n : Nat} (A : Matrix (Fin m) (Fin n) Int) (b : Fin m → Rat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    ∀ (N l w : Nat),
      (∀ (i : Fin m) (j : Fin n),
          @LE.le Nat instLENat (A i j).natAbs
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) l)) →
        (∀ (i : Fin m),
            Lax109476Proofs.RationalArithmeticBounds.Height (b i)
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) l)) →
          @LE.le Nat instLENat (Lax109476Proofs.RamSearchBounds.wordWidth m n N l) w →
            Lax808846Proofs.Reasoning.Spec
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
              (@Lax109476Proofs.RamSearchBounds.Input m n A b N) Lax109476Proofs.RamSearchLoop.search
              (fun (x τ : Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamSearchLoop.Invariant m n A b N τ)
                  (@Eq (Option Nat)
                    (Lax109476Proofs.EllipsoidSearch.findFirst
                      (fun (j : Nat) =>
                        @Decidable.decide
                          (@Eq (Option (Fin m))
                            (@Lax109476Proofs.RationalSeparation.firstViolation m n A b
                              (@Prod.snd (Matrix (Fin n) (Fin n) Rat) (Fin n → Rat)
                                (@Lax109476Proofs.EllipsoidSearch.trajectory m n A b j)))
                            (@Option.none (Fin m)))
                          (@Option.decidableEqNone (Fin m)
                            (@Lax109476Proofs.RationalSeparation.firstViolation m n A b
                              (@Prod.snd (Matrix (Fin n) (Fin n) Rat) (Fin n → Rat)
                                (@Lax109476Proofs.EllipsoidSearch.trajectory m n A b j)))))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
                    (@ite (Option Nat)
                      (@Eq Nat (τ.vars "search.found") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (instDecidableEqNat (τ.vars "search.found")
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Option.some Nat (τ.vars "iter.k")) (@Option.none Nat))))
              (Lax109476Proofs.RamSearchBounds.instructionBound m n N l) := by sorry
