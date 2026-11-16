-- Prove2me | Theorems.Thm_IPEComm1531_Main_Supplement_theorem_B_1
-- name    : IPEComm1531.Main.Supplement.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:15:35.617071+00:00
-- url     : https://prove2.me/theorems/bc1973e8-dadf-48a3-92fd-128e6a400404
-- title:
--   Theorem B.1 — $R(\mathrm{IPE}_n)=\Omega(\log n)$
-- statement:
--   Fix the compatible function spaces $S$, the strong extractor family $E$, and the prescribed-zero functions $p$ from the IPE construction. More generally, let these data satisfy the correctness properties of Theorem 3.2, Fact 2.3, and Lemma 3.3, respectively. Write $\mathrm{IPE}_n=\mathrm{family}(S,E,p,n)$ for the already published total Boolean function on two $n$-bit inputs, with the fixed address map and unused suffix bits ignored.
--
--   There are a real constant $c>0$ and a natural number $N$, depending at most on these fixed construction data, such that for every $n\ge N$ and every public-coin protocol $P$ of worst-case communication cost at most $k$ bits, if Bob outputs $\mathrm{IPE}_n$ with error at most $1/3$ on every input pair, then
--   $$
--   k\ge c\log_2 n.
--   $$
--   Thus $R(\mathrm{IPE}_n)=\Omega(\log n)$. This is the companion lower bound to Theorem 4.1's upper bound, giving matching logarithmic randomized communication complexity for the same family. It is independent of the proof of the mission's goal, Theorem 1.1.
--
--   **Formalization Note** The protocol runs for exactly $k$ communicated bits, which represents an at-most-$k$ worst-case budget by padding. Only Bob must output the answer. The proof on pp.17–18 counts a communicated output bit, so its rectangle count applies after appending that bit, at cost $K=k+1$. Its inequalities permit $c=1/2$ once $N$ is large enough; this statement retains the source's existential constant. There is no effectivity assumption, distributional-only error criterion, input promise, or restriction to tower lengths.
--
--   Differences from the source:
--   - generalization: the specific spaces, extractor and prescribed-zero functions constructed in §3 → every S, E, p satisfying Spaces.Good, Extractors.Good and PrescribedCorrect S p, without algorithmic effectivity assumptions; reason: Appendix B uses only these correctness properties and the fixed address construction; the source construction satisfies them, so this specializes to the full source result
--   - encoding: R(IPE_n) = Ω(log n) → there exist c > 0 and N, fixed before n, k and P, such that every public-coin protocol computing the published family S E p n at Bob with pointwise error at most 1/3 and padded worst-case cost k satisfies k ≥ c log₂ n for all n ≥ N; reason: unpacks the minimum protocol cost and Ω notation using the source base-two logarithm; exact k-bit padding preserves worst-case cost, and the proof can communicate Bob’s output with one extra bit absorbed into the asymptotic constant
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), Theorem B.1, printed/PDF p.17, proof pp.17–18; PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136

import Mathlib
import Definitions.Def_IPEComm1531_Main_Construction
import Definitions.Def_IPEComm1531_Main_Protocol

set_option autoImplicit false
open DistVerif.Simulation

namespace IPEComm1531.Main.Supplement

/-- Theorem B.1 (pp.17–18): the same IPE family has randomized communication
complexity Ω(log n). Correctness properties suffice; no local-computation bound is required.
The constants precede the length and every public-coin protocol. The Bob-local output
convention is the published one; the proof may communicate that output with one extra bit. -/
theorem theorem_B_1 (S : Spaces) (E : Extractors) (p : Prescribed)
    (hS : S.Good) (hE : E.Good) (hp : PrescribedCorrect S p) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, ∀ P : PubProtocol n,
        BobComputesWithin P k (family S E p n) (1 / 3) →
          c * Real.logb 2 n ≤ (k : ℝ) := by sorry

end IPEComm1531.Main.Supplement
