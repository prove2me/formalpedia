-- Prove2me | Theorems.Thm_GaussPart_theorem_3_1
-- name    : GaussPart.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:30.131202+00:00
-- url     : https://prove2.me/theorems/d7e74dc6-9a59-487f-8495-b415ca569522
-- title:
--   Theorem 3.1 — Gaussian partitioning algorithm: thin polyhedral cells matching Gaussian moments, from $d^kB$ samples
-- statement:
--   Let $d,k\ge1$, $q\ge1$, $\sigma\in(0,1]$, $P=N(0,I_d)$, and let $Q$ be a probability distribution on $\mathbb R^d$ that is $(q,\sigma)$-smooth with respect to $P$. There is one algorithm, working for all these parameters, such that given $\eta,\delta,\Delta\in(0,1/2)$ and samples from $Q$ it draws at most $d^kB$ samples, runs in time $d^{O(k)}B$, where
--   $$B=\exp\!\Big(\frac{O((qk)^{O(k)})}{\Delta^{O(1)}}\log^{O(k)}\!\Big(\frac{2}{\sigma\eta}\Big)\log\frac2\delta\Big),$$
--   and with probability at least $2/3$ returns a partition $\mathcal U$ of $\mathbb R^d$ into polyhedral cells with $|\mathcal U|\le B$ and a subcollection $\mathcal G\subseteq\mathcal U$ with $Q\big(\bigcup_{R\in\mathcal G}R\big)\ge1-\eta$, such that every $R\in\mathcal G$ satisfies
--   1. $Q(R)\ge 1/B$;
--   2. $\operatorname{diam}(R)\le\delta$, measured in the span $V_R$ of the cell's constraint normals;
--   3. $P\mid R$ and $Q\mid R$ match their first $k$ directional moments on $V_R^\perp$ with slack $\Delta$.
--
--   This is the paper's main algorithmic result: the number of cells is independent of $d$, and on certified cells the conditional distribution looks Gaussian in the unrestricted directions, which is what the learning applications of §§4–6 use.
--
--   **Formalization Note** The algorithm is one program of the published sampling real RAM restricted to arithmetic instructions (`ArithmeticOnly`), chosen with one natural constant $C$ before all parameters; it reads $d$ and $(k,q,\sigma,\eta,\delta,\Delta)$ and accesses $Q$ only through `sample` (cost $d$). $B$ is `sizeBound C k q σ η δ Δ`; the bounds are samples $\le d^kB$ and work $\le d^{Ck}B$ on every sample stream. The output is decoded from memory (`decodeOutput`) and must satisfy `IsGoodOutput`.
--
--   Differences from the source:
--   - reading: "there is an algorithm" with costs in arithmetic operations and time → one program of the published sampling real RAM restricted by ArithmeticOnly (exact +, −, ×, ÷, rational literals, comparisons, memory, sample, halt; no √, exp, cos, sin, coins), chosen before all parameters and Q, reaching Q only through sample; reason: the paper names no machine and counts "arithmetic operations" (p.35); the literal list is the non-weaker reading (an extra primitive would weaken the theorem)
--   - encoding: O(·) in B and d^{O(k)} → one natural number C chosen with the program: B = exp(C(qk)^{Ck}/Δ^C · log(2/(ση))^{Ck} · log(2/δ)), work ≤ d^{Ck}B; reason: on the stated ranges every factor is ≥ 1, so one constant is equivalent to separate ones
--   - reading: draws at most … samples, runs in time … → the sample and work bounds hold on every sample stream, and every run halts; reason: worst-case reading of the budgets, the stronger one; Algorithm 1's budgets are fixed
--   - reading: polyhedral cell {x : w⁽ⁱ⁾·x ≤ bᵢ} → cells may also carry strict constraints w·x < b; reason: Definition 3.4 cuts ℝ into half-open intervals, and ℝ^d (connected) has no partition into finitely many disjoint nonempty closed cells other than itself
--   - encoding: returns U and G → a memory layout (count, flags, constraint records) decoded by decodeOutput; a malformed output counts as failure; reason: the page fixes no output format
--   - encoding: diam(R) = sup{∥u − v∥ : u, v ∈ proj_{V_R}(R)} ≤ δ → ∥proj_{V_R}x − proj_{V_R}y∥ ≤ δ for all x, y ∈ R; reason: the same condition, without the default value of a supremum over an unbounded set
--   - encoding: with probability at least p → a measurable set of sample streams of i.i.d.-product measure at least p on which every halted state has the property; reason: outer probability of a non-measurable event would be weaker
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 3.1, p.14 (PDF p.16); informal Theorem 1.2, p.2

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_sizeBound
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_decode
import Definitions.Def_GaussPart_IsGoodOutput

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Theorem 3.1** (Gaussian Partitioning Algorithm).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 3.1, p.14 (PDF p.16);
informal version Theorem 1.2, p.2.

"Let k, d ∈ ℕ₊, q ≥ 1, σ ∈ (0, 1]. Let P = N(0, I_d) and suppose that Q is a distribution on ℝ^d that
is (q, σ)-smooth with respect to P. There is an algorithm such that given η, δ, ∆ ∈ (0, 1/2), it draws
at most d^k B samples from Q, runs in time d^{O(k)} B for
B = exp( O((qk)^{O(k)})/∆^{O(1)} log^{O(k)}(2/(ση)) log(2/δ) ), and, with probability at least 2/3,
returns a polyhedral partition U of ℝ^d with |U| ≤ B and a collection G ⊆ U satisfying
Q(⋃_{R∈G} R) ≥ 1 − η. Every R ∈ G satisfies: (i) Q(R) ≥ 1/B. (ii) diam(R) ≤ δ, where the diameter is
measured in the constraint subspace V_R. (iii) P | R and Q | R match their first k directional
moments on V_R^⊥ with slack ∆."

**Formalization Note.**
* The algorithm is one program `P` of the published sampling real RAM `GaussMixHH`, restricted by
  `ArithmeticOnly` to its arithmetic instructions (exact `+ − × ÷`, rational literals, comparisons,
  memory and pointer moves, `sample`, `halt`): no `√`, `exp`, `cos`, `sin`, no coins. It is chosen
  before every parameter and every `Q`; it receives `d` in pointer `0` and `k, q, σ, η, δ, ∆` in
  memory (`goalInput`) and reaches `Q` only through `sample` (cost `d`). The coin tape is fixed
  (`noCoins`); an `ArithmeticOnly` program never reads it.
* `O(·)`: one natural number `C`, chosen with the program, and `B = sizeBound C k q σ η δ ∆`. The
  sample count is at most `d^k B` and the work at most `d^{Ck} B`, on **every** sample stream.
* The output is decoded from memory (`decodeOutput`) as a list of cells with certification flags;
  `IsGoodOutput` is the page's guarantee: a partition (pairwise disjoint, covering), `|U| ≤ B`,
  `Q(⋃_{R∈G} R) ≥ 1 − η`, and (i)–(iii) for every flagged cell, with conditional laws
  `ProbabilityTheory.cond`. A cell is a list of constraints `w · x ≤ b` or `w · x < b`; `V_R` is the
  span of its normals.
* "With probability at least 2/3": a measurable set of sample streams of `Q^{⊗ℕ}`-measure at least
  `2/3` on which every halted state decodes to a good output. -/
theorem theorem_3_1 :
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P) (C : ℕ),
      ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
      ∀ (q σ η δ Δ : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < η → η < 1 / 2 → 0 < δ → δ < 1 / 2 →
        0 < Δ → Δ < 1 / 2 →
      ∀ (Q : Measure (Vec d)) [IsProbabilityMeasure Q], IsSmooth (stdGaussian (Vec d)) Q q σ →
        (∀ xs : ℕ → Vec d, ∃ t : ℕ,
          (GaussMixHH.run P d (GaussMixHH.initState d (goalInput k q σ η δ Δ)) (noCoins, xs) t).halted
              = true ∧
          ((GaussMixHH.run P d (GaussMixHH.initState d (goalInput k q σ η δ Δ)) (noCoins, xs)
              t).samplesUsed : ℝ) ≤ (d : ℝ) ^ k * sizeBound C k q σ η δ Δ ∧
          ((GaussMixHH.run P d (GaussMixHH.initState d (goalInput k q σ η δ Δ)) (noCoins, xs)
              t).work : ℝ) ≤ (d : ℝ) ^ (C * k) * sizeBound C k q σ η δ Δ) ∧
        ∃ E : Set (ℕ → Vec d), MeasurableSet E ∧
          (2 / 3 : ENNReal) ≤ Measure.infinitePi (fun _ : ℕ => Q) E ∧
          ∀ xs ∈ E, ∀ t : ℕ,
            (GaussMixHH.run P d (GaussMixHH.initState d (goalInput k q σ η δ Δ)) (noCoins, xs)
              t).halted = true →
            ∃ L, decodeOutput d (GaussMixHH.run P d (GaussMixHH.initState d (goalInput k q σ η δ Δ))
                (noCoins, xs) t) = some L ∧
              IsGoodOutput Q k η δ Δ (sizeBound C k q σ η δ Δ) L := by sorry

end GaussPart
