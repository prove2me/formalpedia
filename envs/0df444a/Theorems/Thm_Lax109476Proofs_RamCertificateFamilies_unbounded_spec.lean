-- Prove2me | Theorems.Thm_Lax109476Proofs_RamCertificateFamilies_unbounded_spec
-- name    : Lax109476Proofs.RamCertificateFamilies.unbounded_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:10:39.915026+00:00
-- url     : https://prove2.me/theorems/023aa797-0ab8-4249-9b7c-25d5c76de2b2
-- title:
--   Execution of unboundedness-certificate system construction
-- statement:
--   Let $P=(A,b,c)$ be an integer linear program with $m$ constraints and $n$ variables. Let $M\ge1$ bound the absolute values of all entries, and let $B>M$ be the machine modulus. Put $r=2m+1$ and $s=2n$. Assume
--   $$mn+2m+2n+8<B,\qquad rs+r+s+4<B.$$
--   Given the stored source program and allocated target arrays of lengths $rs$ and $r$, the unboundedness-family command writes the exact matrix and right-hand side of the published ray-certificate system $F_{\rm unb}(P)$ and preserves the source representation. Its actual execution satisfies
--   $$T\le134rs+90r+74.$$
--   The statement includes zero-dimensional inputs. It provides the operational construction needed before deciding and recovering an unboundedness certificate.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamCertificateFamilies.lean, theorem unbounded_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces

theorem Lax109476Proofs.RamCertificateFamilies.unbounded_spec : ∀ (B M m n : ℕ) (P : Lax109476.LinearProgram.Program ℤ m n),
  1 ≤ M →
    M < B →
      m * n + 2 * m + 2 * n + 8 < B →
        (m + (m + 1)) * (n + n) + (m + (m + 1)) + (n + n) + 4 < B →
          (∀ (i : Fin m) (j : Fin n), (P.A i j).natAbs ≤ M) →
            (∀ (i : Fin m), (P.b i).natAbs ≤ M) →
              (∀ (j : Fin n), (P.c j).natAbs ≤ M) →
                Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamCertificateFamilies.Input P (m + (m + 1)) (n + n))
                  Lax109476Proofs.RamCertificateFamilies.unbounded
                  (fun (x τ : Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamCertificateSource.Data P τ ∧
                      Lax109476Proofs.RamEquationData.Data (Lax109476Proofs.CertificateFamilyPrograms.unbounded P) τ)
                  (134 * ((m + (m + 1)) * (n + n)) + 90 * (m + (m + 1)) + 74) := by sorry
