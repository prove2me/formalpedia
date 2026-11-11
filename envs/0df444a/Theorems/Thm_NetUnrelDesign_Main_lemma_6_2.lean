-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_6_2
-- name    : NetUnrelDesign.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:53.857205+00:00
-- url     : https://prove2.me/theorems/7a8a9769-7462-4670-b0a7-4434b9b5cb69
-- title:
--   Lemma 6.2 — on the prepared data, a 3/4-success candidate trial and a 63/64-accurate value estimate with costs (6.2)/(6.3)
-- statement:
--   Fix the absolute constant $\gamma$ of (5.6) and a marked-source constant $C_Z$. There are a constant $C$ and two programs with a marked-source instruction, a candidate trial and a value estimate. They work **on the prepared data**:
--   - an instance satisfying (1.1), with $0<\varepsilon\le1/2$ and $a=\varepsilon/16$;
--   - the second output $(x^0,\lambda_0,J,\bar x)$ of Lemma 5.1 for some threshold $0<\eta<1$, satisfying (5.2), (5.3) and (5.6);
--   - the domain $D=Q_0$ if the branch test (5.8) holds, and $D=X_D$ with $D=\log(e^22^{38}m^9/\varepsilon^3)$ if it fails;
--   - when (5.8) fails, also a Burg center $c$ satisfying (D.3), and a marked source valid for (3.1) with $C_Z$, with expected cost at most $Q\ge m$ at every feasible point of risk at least $\varepsilon^2/(e^22^{30}m^8)$.
--
--   On these data:
--   1. The candidate trial returns a point of $D$ or FAIL on every halting run, with $\Pr\{x\ne{\rm FAIL},\ u(x)\le(1+a)u^*\}\ge3/4$.
--   2. At any $x\in D$, the value estimate returns $W$ with $\Pr\{|W-u(x)|\le a\,u(x)\}\ge63/64$.
--
--   The expected cost of each call is uniformly bounded, by $C(mQ+km^2)\varepsilon^{-2}L^4h$ (6.2) when the branch test fails and by $C(km^2L+m^3L^4)$ (6.3) when it holds. Every call uses fresh randomness.
--
--   Differences from the source:
--
--   - reading: 'On these prepared data' → explicit hypotheses: an instance with (1.1), 0 < ε ≤ 1/2, a Lemma 5.1 output (x⁰, λ₀, J, x̄) with (5.2), (5.3), (5.6) for some threshold 0 < η < 1 and the constant γ, D chosen by (5.8), and in the failing branch a Burg center with (D.3) and the marked source of Theorem 6.1 (valid with C_Z at every design, cost ≤ Q ≥ m at feasible points of risk at least ε²/(e²2³⁰m⁸)); reason: these are the data §6 prepares before stating the lemma
--   - encoding: two routines; FAIL → two Admissible programs of the machine with the marked-source instruction, inputs as listed; FAIL = integer output cell 0 equal to 0; reason: the paper's routines made explicit
--   - encoding: O(·) in (6.2), (6.3) → one constant C, chosen after γ and C_Z and before all other data; reason: γ and C_Z are the paper's absolute constants
--   - encoding: 'the conditional expected cost of each call is uniformly bounded' → the expected work of each program run (one call = one run on fresh tapes) is at most the bound, for the candidate trial and for the value estimate at every x ∈ D; reason: every call uses fresh randomness, so the conditional cost is the cost of a fresh run
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 6.2, p. 18 (PDF 19)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators ENNReal Classical

namespace NetUnrelDesign.Main

/-- **Lemma 6.2 (Relative computation after preparation).** For every value of the absolute
constant `γ` of (5.6) and every marked-source constant `C_Z`, there are a constant `C` and two
programs with a marked-source instruction (a candidate trial and a value estimate) such that, on
the prepared data — an instance satisfying (1.1), `0 < ε ≤ 1/2`, the second output
`(x⁰, λ₀, J, x̄)` of Lemma 5.1 for some threshold `0 < η < 1` ((5.2), (5.3), (5.6)), `a = ε/16`,
the domain `D = Q₀` if (5.8) holds and `D = X_D` with `D = log(e²2³⁸m⁹/ε³)` if it fails, in which
case also a Burg center `c` with (D.3), a marked source valid for (3.1) with `C_Z` and a cost bound
`Q ≥ m` on every feasible point of risk at least `ε²/(e²2³⁰m⁸)` — :
(1) the candidate trial returns a point of `D` or FAIL on every halting run, and returns a point
`x` with `u(x) ≤ (1 + a)u*` with probability at least `3/4`;
(2) at any `x ∈ D` the value estimate returns `W` with `|W − u(x)| ≤ a u(x)` with probability at
least `63/64`;
each with expected cost at most `C(mQ + km²)ε⁻²L⁴h` (6.2) when (5.8) fails and
`C(km²L + m³L⁴)` (6.3) when it holds. Every call runs on fresh randomness.
Sun 2026, p. 18 (PDF 19). -/
theorem lemma_6_2 :
    ∀ γ : ℝ, 0 < γ → ∀ CZ : ℝ, 0 < CZ →
      ∃ C : ℝ, 0 < C ∧ ∃ Pc Pv : Program, Admissible Pc ∧ Admissible Pv ∧
        ∀ {n m k : ℕ} (I : Instance n m k), I.Standing →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
            ∀ (η : ℝ), 0 < η → η < 1 →
              ∀ (x0 : Fin m → ℝ) (lam0 : ℝ) (J : Matrix (Fin m) (Fin m) ℝ) (xbar : Fin m → ℝ),
                PrepData I η γ x0 lam0 J xbar →
                ∀ c : Fin m → ℝ, (¬ BranchHolds n ε lam0 → BurgCenter I (boxWidth m ε) c) →
                ∀ (O : Oracle (markedSpec n m)) (Q : ℝ),
                  (¬ BranchHolds n ε lam0 →
                    MarkedValid I.ends I.q0 CZ O ∧ (m : ℝ) ≤ Q ∧
                    ∀ x ∈ I.feasible, riskFloor m ε ≤ I.u x → MarkedCostAt Q O x) →
                  OnEveryHalt Pc O
                      (initState (markedSpec n m) (instInts I)
                        ([ε] ++ instReals I ++ [lam0] ++ vecList x0 ++ vecList xbar ++
                          matList J ++ vecList c))
                      (fun s => outInt s 0 ≠ 0 → outVec s 0 m ∈ candDomain I ε lam0) ∧
                  failureProb Pc O
                      (initState (markedSpec n m) (instInts I)
                        ([ε] ++ instReals I ++ [lam0] ++ vecList x0 ++ vecList xbar ++
                          matList J ++ vecList c))
                      (fun s => outInt s 0 ≠ 0 ∧
                        I.u (outVec s 0 m) ≤ (1 + aPar ε) * I.uStar) ≤ ENNReal.ofReal (1 / 4) ∧
                  expectedWork Pc O
                      (initState (markedSpec n m) (instInts I)
                        ([ε] ++ instReals I ++ [lam0] ++ vecList x0 ++ vecList xbar ++
                          matList J ++ vecList c)) ≤
                    ENNReal.ofReal (if BranchHolds n ε lam0 then
                      C * ((k : ℝ) * m ^ 2 * Lrate m k ε + (m : ℝ) ^ 3 * Lrate m k ε ^ 4) else
                      C * ((m : ℝ) * Q + (k : ℝ) * m ^ 2) * ε⁻¹ ^ 2 * Lrate m k ε ^ 4 *
                        logTwoM m) ∧
                  ∀ x ∈ candDomain I ε lam0,
                    failureProb Pv O
                        (initState (markedSpec n m) (instInts I)
                          ([ε] ++ instReals I ++ [lam0] ++ vecList x0 ++ vecList xbar ++
                            matList J ++ vecList c ++ vecList x))
                        (fun s => |outReal s 0 - I.u x| ≤ aPar ε * I.u x) ≤
                      ENNReal.ofReal (1 / 64) ∧
                    expectedWork Pv O
                        (initState (markedSpec n m) (instInts I)
                          ([ε] ++ instReals I ++ [lam0] ++ vecList x0 ++ vecList xbar ++
                            matList J ++ vecList c ++ vecList x)) ≤
                      ENNReal.ofReal (if BranchHolds n ε lam0 then
                        C * ((k : ℝ) * m ^ 2 * Lrate m k ε + (m : ℝ) ^ 3 * Lrate m k ε ^ 4) else
                        C * ((m : ℝ) * Q + (k : ℝ) * m ^ 2) * ε⁻¹ ^ 2 * Lrate m k ε ^ 4 *
                          logTwoM m) := by sorry

end NetUnrelDesign.Main
