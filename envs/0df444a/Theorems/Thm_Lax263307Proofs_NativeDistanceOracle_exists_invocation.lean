-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeDistanceOracle_exists_invocation
-- name    : Lax263307Proofs.NativeDistanceOracle.exists_invocation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:56:02.132279+00:00
-- url     : https://prove2.me/theorems/63b53375-bcdd-4e29-b2d5-286236439c9f
-- title:
--   Fixed native distance-LP construction and solver invocation
-- statement:
--   Let $f$ be a polynomial-time word-RAM function on finite word lists. One fixed native program and natural polynomials for its word width and time implement every distance-LP query. For a rational program $P$, rational center $x$, and query $Q=\operatorname{encode}(\operatorname{distanceLP}(P,x))$, the output is exactly $f(Q)$.
--
--   The complete call is valid under the stated source-height, word-width, input-size, polynomial-evaluation and workspace guards. It preserves the encoded source program and center, returns a halted virtual solver state, and satisfies the explicit native distance-oracle instruction bound. The same finite program and polynomial bounds precede every program and center. This is the construction-and-simulation part of the exact native projection interface.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeDistanceOracle.lean, theorem exists_invocation

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces

theorem Lax263307Proofs.NativeDistanceOracle.exists_invocation : ∀ (f : List ℕ → List ℕ),
  Lax759944.RamPolytime.RamPolytime f →
    ∃ (p : Lax808846.Ram.Program) (wp : Polynomial ℕ) (tp : Polynomial ℕ) (coeff : List ℕ),
      (∀ (z : ℕ), Lax455465Proofs.RamPolynomial.value coeff z = Polynomial.eval z wp) ∧
        ∀ (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (x : Fin n → ℚ),
          have query := Lax109476.RationalEncoding.encodeProgram (Lax263307.DistanceProjection.distanceProgram P x);
          Lax759944.RamPolytime.FitsInWords (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query) wp)
              (query.length :: query ++ f query) ∧
            ∀ (B : ℕ),
              Lax263307Proofs.NativeDistanceData.shapeSize m n < B →
                Lax263307Proofs.NativeDistanceData.Bounded B P x →
                  Lax759944.BinaryWordEncoding.bitSize query + 1 < B →
                    Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query + 1) wp < B →
                      2 * (2 ^ Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query) wp) ^ 2 + 3 < B →
                        Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query) tp + 1 < B →
                          Lax455465Proofs.RamVirtualConstants.allowance p < B →
                            Lax808846Proofs.Reasoning.Spec B
                              (fun (σ : Lax808846Proofs.Imp.Env) =>
                                Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeProgram P)
                                    "lp.input" σ ∧
                                  Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeVector x)
                                      "projection.center" σ ∧
                                    Lax263307Proofs.NativeDistanceData.wordLength m n < (σ.arrs "lp.word").length ∧
                                      query.length < (σ.arrs "vm.input").length ∧
                                        Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query) tp <
                                            (σ.arrs "vm.addresses").length ∧
                                          Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query) tp <
                                              (σ.arrs "vm.values").length ∧
                                            Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query) tp <
                                              (σ.arrs "vm.output").length)
                              (Lax263307Proofs.NativeDistanceOracle.command p coeff)
                              (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                                Lax455465Proofs.RamVirtualState.Prefix (f query) "vm.output" τ ∧
                                  τ.vars "vm.outputLength" = (f query).length ∧
                                    τ.vars "vm.running" = 0 ∧
                                      Lax455465Proofs.RamVirtualState.Prefix
                                          (Lax109476.RationalEncoding.encodeProgram P) "lp.input" τ ∧
                                        Lax455465Proofs.RamVirtualState.Prefix
                                          (Lax109476.RationalEncoding.encodeVector x) "projection.center" τ)
                              (Lax263307Proofs.NativeDistanceOracle.cost m n p coeff
                                (Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize query) tp)
                                (Lax759944.BinaryWordEncoding.bitSize query)) := by sorry
