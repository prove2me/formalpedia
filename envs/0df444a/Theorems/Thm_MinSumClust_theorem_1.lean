-- Prove2me | Theorems.Thm_MinSumClust_theorem_1
-- name    : MinSumClust.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:33.901704+00:00
-- url     : https://prove2.me/theorems/97c364e0-897f-47a4-8baf-b4c7aa7aa6b3
-- title:
--   Theorem 1 — a randomized polynomial-time $(2.16\times10^9+\varepsilon)$-approximation for min-sum $k$-clustering
-- statement:
--   For every $\varepsilon>0$ there are a polynomial $p$ and a polynomial-time algorithm that reads a min-sum $k$-clustering instance $I$ and a string of $p(|\mathrm{enc}(I)|)$ fair coins and, on every well-formed instance,
--
--   1. outputs a partition of the clients into exactly $k$ nonempty clusters for **every** coin string, and
--   2. has expected cost
--   $$\mathbb E_{w}\bigl[\mathrm{cost}(\mathrm{ALG}(I,w))\bigr]\ \le\ (2.16\times10^{9}+\varepsilon)\cdot\mathrm{opt}(I),$$
--   the expectation being over uniform coin strings.
--
--   Well-formed instances are all finite rational metrics on $n\ge 1$ clients with $1\le k\le n$; the cost of a clustering is the sum of $d(i,j)$ over ordered pairs in the same cluster, and $\mathrm{opt}$ is the least cost of a partition into exactly $k$ nonempty clusters. This answers the question, open since Bartal, Charikar and Raz (STOC 2001), whether min-sum $k$-clustering admits a constant-factor approximation in polynomial time.
--
--   Differences from the source:
--
--   - reading: a randomized polynomial-time algorithm → ∃ polynomial p and a Mathlib Turing.TM2ComputableInPolyTime machine from encInstCoins (instance and coin string, binary) to encLabels; coins uniform on strings of length p(|enc I|); reason: the paper names no machine model; randomness as a coin string read by a deterministic machine
--   - reading: a (2.16×10⁹+ε)-approximation → for every ε > 0 one algorithm, feasible on every coin string, whose expected cost is at most (2.16×10⁹ + ε)·opt; reason: Theorem 3 and Claim 60 bound the expected cost, and A.1 fixes ε inside the algorithm's stopping rule
--   - encoding: clients D with metric distances, clusterings → clients Fin n, rational distances in binary, ordered-pair cost, outputs as labellings; malformed encoded inputs may get any output; reason: Lean convention; every finite input of the problem is such an instance (footnote 1: ordered vs. unordered pairs is irrelevant)
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Theorem 1, p.1 (PDF p.3); proof in Appendix A.1, p.62 (PDF p.64)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_MinSumClust_Inst
import Definitions.Def_MinSumClust_opt
import Definitions.Def_MinSumClust_encInst
import Definitions.Def_MinSumClust_coinAvg

namespace MinSumClust

/-- **Theorem 1 (main result)**, p.1 (PDF p.3).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Theorem 1, p.1: "There is a randomized polynomial-time
(2.16×10⁹+ε)-approximation for the min-sum k-clustering problem."

For every `ε > 0` there are a polynomial `p` and a polynomial-time machine reading an instance and
a coin string such that, on every well-formed instance `I`, the output is a partition of the
clients into exactly `k` nonempty clusters for **every** coin string of length `p(|enc I|)`, and
the expected cost over uniform coins is at most `(2.16 × 10⁹ + ε) · opt`.

**Formalization Note.** The paper names no machine. "Randomized polynomial-time" is Mathlib's
`Turing.TM2ComputableInPolyTime` from `encInstCoins` (instance and coin string, binary) to
`encLabels` (a labelling), with coins uniform on strings of length `p(|enc I|)` (`coinAvg`, the exact
average). The cost counts ordered pairs, and `opt` is the minimum over partitions into exactly `k`
nonempty clusters. `ε` is real and fixed before the machine; `p` and the machine come before the
instance. Malformed encoded inputs may get any output. -/
theorem theorem_1 :
    ∀ ε : ℝ, 0 < ε →
      ∃ (p : Polynomial ℕ) (alg : Inst × List Bool → List ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encLabels alg) ∧
        ∀ I : Inst, I.WellFormed →
          (∀ w : List Bool, w.length = p.eval (encInst I).length →
              IsKClustering I (alg (I, w))) ∧
            coinAvg I p (fun w => labelCost I (alg (I, w))) ≤ (2160000000 + ε) * opt I := by sorry

end MinSumClust
