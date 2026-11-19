-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSelectedLP_exists_program
-- name    : Lax263307Proofs.NativeSelectedLP.exists_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:11.592925+00:00
-- url     : https://prove2.me/theorems/15005a04-5201-43be-a416-384cd36f48d4
-- title:
--   A native rational projection oracle from one selected LP solver
-- statement:
--   Every exact polynomial-time word-RAM LP solver admits a fixed native projection-oracle implementation with polynomial resource bounds:
--   $$\operatorname{Nonempty}(\operatorname{Program}(f)).$$
--   The program uses the same selected LP backend for its width guarantee and actual invocation; it retains the encoded query and classifies the exact certificate.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedLP.lean, theorem exists_program

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax263307Proofs.NativeSelectedLP.exists_program : ∀ (f : List ℕ → List ℕ),
  Lax759944.RamPolytime.RamPolytime f →
    Lax263307Proofs.NativeEncodedLP.Encoded f → Nonempty (Lax263307Proofs.NativeSelectedLP.Program f) := by sorry
