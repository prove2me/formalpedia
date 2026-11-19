-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSelectedNear_exists_program
-- name    : Lax263307Proofs.NativeSelectedNear.exists_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:10:21.662004+00:00
-- url     : https://prove2.me/theorems/933b984f-db3a-4eec-8bfd-9b40df8cdcd1
-- title:
--   Finite native separator-call adapter for a polynomial RAM function
-- statement:
--   Let $f$ be a function from finite natural-number word lists to such lists, computed by one polynomial-time word-RAM program. Then there is one native separator-call program record for $f$:
--   $$\operatorname{RamPolytime}(f)\ \Longrightarrow\ \exists\,\mathcal P_f.$$
--   The record contains fixed finite code, polynomial width, time and output bounds, and an explicit encoding of the width polynomial. On each graph and rational-load input meeting its height and workspace guards, the actual call preserves the separator context and writes exactly the remaining mask, separator mask, cut count, cut records and piece records decoded from $f$'s result. Its time is the record's explicit call bound. This adapter lets the selected polynomial flow routine participate in the native recursive algorithm.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedNear.lean, theorem exists_program

import Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces

theorem Lax263307Proofs.NativeSelectedNear.exists_program : ∀ (f : List ℕ → List ℕ), Lax759944.RamPolytime.RamPolytime f → Nonempty (Lax263307Proofs.NativeSelectedNear.Program f) := by sorry
