-- Prove2me | Theorems.Thm_MCPoise_lemma_2_1
-- name    : MCPoise.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:33:29.668894+00:00
-- url     : https://prove2.me/theorems/17d3866b-ecbd-4acb-a7a0-cf388dc11035
-- title:
--   Lemma 2.1 — Junction-LP is solved in polynomial time, with polynomial support
-- statement:
--   **Lemma 2.1.** There is a polynomial-time algorithm which takes an instance and a value $L$ and outputs a rational vector $(x, f, \lambda)$ with at most $\mathrm{poly}(n + k)$ entries, such that the vector is feasible for Junction-LP whenever $L$ is certified.
--
--   The program has exponentially many path variables; this lemma is the starting point of the rounding.
--
--   Differences from the source:
--   - reading: an efficient, polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, polynomial in a fixed binary encoding on every input; reason: the source names no machine, and every step it describes is deterministic
--   - generalization: $L$ is the value of the optimal solution → $L$ is an input and the guarantee holds for every $L$ with a certifying subgraph; reason: an optimal solution certifies its own poise, so this contains $L = \mathrm{OPT}$; the proof uses only the certificate (p.35)
--   - encoding: polynomial support size → the number of output entries is at most a fixed polynomial of n + k; reason: the feasible support is polynomial in n and k, and each entry is listed
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.1, p.10

import Mathlib
import Definitions.Def_MCPoise_WitnessFor
import Definitions.Def_MCPoise_JunctionLPFeasible
import Definitions.Def_MCPoise_JLPOut

namespace MCPoise

/-- **Lemma 2.1 (solving Junction-LP).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.1, p.10: "Junction-LP has a feasible fractional solution with polynomial support size that can be found in polynomial
time." The page: "The feasibility of this LP follows from Theorem 1.6."

One Turing machine, on input `(I, L)` and in time polynomial in the input length, outputs a sparse rational vector; whenever `L` is
certified it is feasible for Junction-LP, and the number of its entries is at most a fixed polynomial of `n + k`.

**Formalization Note.** `L` is an input in binary (p.6: "we guess the value L"), and the machine halts in polynomial time on every `L`. -/
theorem lemma_2_1 :
    ∃ alg : Inst × ℕ → JLPOut,
      Nonempty (Turing.TM2ComputableInPolyTime encLIn encJLPOut alg) ∧
      ∃ p : Polynomial ℕ, ∀ (I : Inst) (L : ℕ) (Hstar : SimpleGraph (Fin I.n)),
        WitnessFor I L Hstar →
        JunctionLPFeasible I L (alg (I, L)).xVal (alg (I, L)).x'Val (alg (I, L)).lamVal
          (alg (I, L)).fVal ∧
        (alg (I, L)).x.length + (alg (I, L)).x'.length + (alg (I, L)).lam.length +
          (alg (I, L)).f.length ≤ p.eval (I.n + I.k) := by sorry

end MCPoise
