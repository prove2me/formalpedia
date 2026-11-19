-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRecoverFeasibleSystem_recover_spec
-- name    : Lax109476Proofs.RamRecoverFeasibleSystem.recover_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:10:31.77086+00:00
-- url     : https://prove2.me/theorems/6f06d497-8307-4446-b2f2-315b2115e163
-- title:
--   Execution of bounded rational feasible-point recovery
-- statement:
--   Let $P=(A,b,c)$ be an integer program with $m$ constraints and $n$ variables whose rational constraint system has a feasible point. Let $m+n\le S$, assume the entries of $A,b$ have absolute value at most $2^{2S}$, and let the word width $w$ meet the published recovery-width bound. Let the allocated reconstruction stack length $N$ be at least the reconstruction-depth bound for the recovery precision, plus one.
--
--   From the encoded recovery input, the command produces a vector $z\in\mathbb Q^{n+m}$ and a complete persistent recovery state such that
--   $$P\text{ is feasible at }(z_0,\ldots,z_{n-1}),\qquad \operatorname{height}(z_j)\le\kappa(m,n,2^{2S})\quad(0\le j<n+m).$$
--   Here $\kappa$ is the published integer-certificate coordinate bound, and height bounds numerator magnitude and positive denominator. The execution uses at most the explicit recovery instruction bound for $(m,n,S)$. All allocated array and stack conditions are retained in the input predicate. This result recovers an actual bounded rational witness rather than only a feasibility decision.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoverFeasibleSystem.lean, theorem recover_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces

theorem Lax109476Proofs.RamRecoverFeasibleSystem.recover_spec : ∀ (m n S N w : ℕ) (P : Lax109476.LinearProgram.Program ℤ m n),
  m + n ≤ S →
    Lax109476Proofs.RamRecoverFeasibleSystem.wordWidth m n S ≤ w →
      Lax109476Proofs.RamRationalReconstruction.depthBound (Lax109476Proofs.RamRecoverFeasibleSystem.recoveryBits S) +
            1 ≤
          N →
        (∀ (i : Fin m) (j : Fin n), (P.A i j).natAbs ≤ 2 ^ (2 * S)) →
          (∀ (i : Fin m), (P.b i).natAbs ≤ 2 ^ (2 * S)) →
            (∃ (x : Fin n → ℚ),
                Lax109476.LinearProgram.PrimalFeasible (Lax109476Proofs.IntegerEncoding.rationalProgram P) x) →
              Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax109476Proofs.RamRecoverFeasibleSystem.Input P S N)
                Lax109476Proofs.RamRecoverFeasibleSystem.recover
                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                  ∃ (z : Fin (n + m) → ℚ),
                    Lax109476Proofs.RamRecoveryThreshold.Persistent
                        (Lax109476Proofs.RamStandardPointRecovery.program
                          (Lax109476Proofs.IntegerPointRecovery.slackMatrix P) P.b)
                        z (n + m) τ ∧
                      (Lax109476.LinearProgram.PrimalFeasible (Lax109476Proofs.IntegerEncoding.rationalProgram P)
                          fun (j : Fin n) => z (Fin.castAdd m j)) ∧
                        ∀ (j : Fin (n + m)),
                          Lax109476Proofs.RationalArithmeticBounds.Height (z j)
                            (Lax109476Proofs.IntegerCertificates.coordinateCap m n (2 ^ (2 * S))))
                (Lax109476Proofs.RamRecoverFeasibleSystem.instructionBound m n S) := by sorry
