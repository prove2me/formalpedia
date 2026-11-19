-- Prove2me | Theorems.Thm_Lax109476Proofs_RamCertificateFamilies_optimal_spec
-- name    : Lax109476Proofs.RamCertificateFamilies.optimal_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:10:36.168639+00:00
-- url     : https://prove2.me/theorems/7055ab14-8aef-4eb3-9f88-64c2edd8668d
-- title:
--   Execution of optimality-certificate system construction
-- statement:
--   Let $P=(A,b,c)$ be an integer linear program with $m$ constraints and $n$ variables. Let $M\ge1$ bound the absolute values of all entries, and let $B>M$ be the machine modulus. Put $r=m+n+2$ and $s=n+m$. Assume
--   $$mn+2m+2n+8<B,\qquad rs+r+s+4<B.$$
--   Given the stored source program and allocated target arrays of lengths $rs$ and $r$, the optimality-family command constructs precisely the matrix and right-hand side of the published certificate system $F_{\rm opt}(P)$, preserving the source representation. Its actual execution satisfies
--   $$T\le142rs+98r+72.$$
--   Empty row or column dimensions are permitted. This specification supplies the operational construction of the certificate family used by the exact LP solver.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamCertificateFamilies.lean, theorem optimal_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces

theorem Lax109476Proofs.RamCertificateFamilies.optimal_spec : ∀ (B M m n : ℕ) (P : Lax109476.LinearProgram.Program ℤ m n),
  1 ≤ M →
    M < B →
      m * n + 2 * m + 2 * n + 8 < B →
        (m + (n + 2)) * (n + m) + (m + (n + 2)) + (n + m) + 4 < B →
          (∀ (i : Fin m) (j : Fin n), (P.A i j).natAbs ≤ M) →
            (∀ (i : Fin m), (P.b i).natAbs ≤ M) →
              (∀ (j : Fin n), (P.c j).natAbs ≤ M) →
                Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamCertificateFamilies.Input P (m + (n + 2)) (n + m))
                  Lax109476Proofs.RamCertificateFamilies.optimal
                  (fun (x τ : Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamCertificateSource.Data P τ ∧
                      Lax109476Proofs.RamEquationData.Data (Lax109476Proofs.CertificateFamilyPrograms.optimal P) τ)
                  (142 * ((m + (n + 2)) * (n + m)) + 98 * (m + (n + 2)) + 72) := by sorry
