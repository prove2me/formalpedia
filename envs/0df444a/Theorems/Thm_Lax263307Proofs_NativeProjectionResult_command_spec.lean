-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeProjectionResult_command_spec
-- name    : Lax263307Proofs.NativeProjectionResult.command_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:55:58.075449+00:00
-- url     : https://prove2.me/theorems/c36c402c-bc6d-48ed-8a1a-f40c6a093d58
-- title:
--   Native processing of an exact distance-LP certificate
-- statement:
--   Let $P$ be a rational program with $m$ rows and $n$ variables, $\rho$ a rational tolerance, and $c$ a certificate for its distance program. Assume the certificate and tolerance meet the stated height bound $M$, the host bound satisfies $2M^2+3<B$ and $3m+10n+20<B$, and the declared storage is available.
--
--   The actual certificate-processing command returns exactly the classified projection outcome for $(P,\rho,c)$, preserves the encoded source program, and records the correct dimension $n$. Its execution has at most the published projection-result cost $C(M,n)$. The output includes the stored near point, separating cut, or rejection data required by that outcome. This interface converts the solver certificate into the rational query result used by the oracle.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeProjectionResult.lean, theorem command_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces

theorem Lax263307Proofs.NativeProjectionResult.command_spec : ∀ (B M m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n)
  (c : Lax109476.RationalCertificates.Certificate (m + (n + n)) (n + 1)) (ρ : ℚ),
  2 * M ^ 2 + 3 < B →
    3 * m + 10 * n + 20 < B →
      Lax263307Proofs.NativeProjectionResult.CertificateBounded M c →
        Lax263307Proofs.NativeSignedArithmetic.Bounded M ρ →
          Lax808846Proofs.Reasoning.Spec B
            (fun (σ : Lax808846Proofs.Imp.Env) =>
              Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeProgram P) "lp.input" σ ∧
                Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeCertificate c) "vm.output" σ ∧
                  Lax263307Proofs.NativeSignedArithmetic.Stored "projection.tolerance" ρ σ ∧
                    3 * n < (σ.arrs "lp.word").length)
            Lax263307Proofs.NativeProjectionResult.command
            (fun (x τ : Lax808846Proofs.Imp.Env) =>
              Lax263307Proofs.NativeProjectionResult.Output (Lax263307.RationalProjection.classify P ρ c) τ ∧
                Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeProgram P) "lp.input" τ ∧
                  τ.vars "projection.n" = n)
            (Lax263307Proofs.NativeProjectionResult.cost M n) := by sorry
