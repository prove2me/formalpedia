-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeMomentVectors_read_spec_native
-- name    : Lax263307Proofs.NativeMomentVectors.read_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:12.065181+00:00
-- url     : https://prove2.me/theorems/8712e4e5-6ae3-4dcc-8020-7936b1787bf3
-- title:
--   Reading a moment-vector entry
-- statement:
--   Let $N,q,B$ be natural numbers with $q+N+4<B$. From a state whose fill index is $q$ and catalog count is $N$, the fixed moment-vector reader returns the specified rational entry $v(N,q)$ within
--   $$T\le18$$
--   bounded operational steps. Its output is represented by the standard signed fraction fields.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeMomentVectors.lean#L41

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
namespace Lax263307Proofs.NativeMomentVectors
end Lax263307Proofs.NativeMomentVectors

theorem Lax263307Proofs.NativeMomentVectors.read_spec_native : ∀ (B N q : Nat),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) q N)
        (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      B →
    Lax808846Proofs.Reasoning.Spec B
      (fun (σ : Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "fill.i") q) (@Eq Nat (σ.vars "catalog.count") N))
      Lax263307Proofs.NativeMomentVectors.read
      (fun (x τ : Lax808846Proofs.Imp.Env) =>
        Lax263307Proofs.NativeMomentProduce.Value B (Lax263307Proofs.NativeMomentVectors.value N q) τ)
      (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) := by sorry
