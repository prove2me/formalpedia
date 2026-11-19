-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeRoundedStep_exists_program
-- name    : Lax263307Proofs.NativeRoundedStep.exists_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:44.344202+00:00
-- url     : https://prove2.me/theorems/fe8fef9e-b38a-456f-82b2-09837e04a8ce
-- title:
--   A native polynomial-time rounded ellipsoid step
-- statement:
--   One fixed RAM program performs the rational rounded ellipsoid update. There is a positive constant $c$ such that valid dimension-$n$ states, integer separating normals, and height parameter $h$ satisfy
--   $$t\le c(n+h+k+1)^{12}$$
--   for the actual instruction count and sufficient host word width. The output is the exact prescribed rounded update, including both center and shape matrix.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRoundedStep.lean, theorem exists_program

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax263307Proofs.NativeRoundedStep.exists_program : ∃ (p : Lax808846.Ram.Program) (c : ℕ),
  0 < c ∧
    ∀ (n k h : ℕ),
      2 ≤ n →
        1 ≤ h →
          ∀ (state : Lax263307.RoundedOracleSearch.State n) (a : Fin n → ℤ),
            (∀ (i j : Fin n), Lax263307.NativeRoundedStep.height (state.1 i j) h) →
              (∀ (i : Fin n), Lax263307.NativeRoundedStep.height (Lax263307.RoundedOracleSearch.rationalNormal a i) h) →
                (∀ (i : Fin n), Lax263307.NativeRoundedStep.height (state.2 i) h) →
                  0 <
                      Lax263307.RoundedOracleSearch.rationalNormal a ⬝ᵥ
                        state.1.mulVec (Lax263307.RoundedOracleSearch.rationalNormal a) →
                    ∀ (w : ℕ),
                      c * (n + h + k + 1) ^ 12 ≤ w →
                        ∃ t ≤ c * (n + h + k + 1) ^ 12,
                          Lax808846.Ram.RunsTo w p (Lax263307.NativeRoundedStep.encodeInput k state a)
                            (Lax263307.NativeRoundedStep.encodeOutput (Lax263307.RoundedOracleSearch.update k state a))
                            t := by sorry
