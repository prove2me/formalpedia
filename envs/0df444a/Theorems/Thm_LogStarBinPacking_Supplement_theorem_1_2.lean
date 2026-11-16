-- Prove2me | Theorems.Thm_LogStarBinPacking_Supplement_theorem_1_2
-- name    : LogStarBinPacking.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:16:43.303181+00:00
-- url     : https://prove2.me/theorems/f9088b23-8565-465e-96ae-5dfcaf0c8c62
-- title:
--   Theorem 1.2 — a universal reduction to three items near $1/3$ preserving the configuration-LP gap
-- statement:
--   For a bin packing instance $I$ (items with sizes $s_I(i)\in(0,1]$) let $\mathrm{OPT}(I)$ be the least number of bins, and let $\mathrm{LP}(I)$ be the value of the configuration LP
--   $$
--   \mathrm{LP}(I)=\min\Big\{\sum_{U\in\mathcal H(I)}y_U:\ y\ge0,\ \sum_{U\ni i}y_U\ge1\ \ \forall i\in I\Big\},\qquad \mathcal H(I)=\{U\subseteq I:\ s_I(U)\le1\}.
--   $$
--
--   For every $\varepsilon>0$ there is a polynomial-time algorithm which, given any bin packing instance $I$, produces a bin packing instance $J$ of $3M$ items, where $M\ge1$ is an integer, with all sizes in
--   $$
--   \Big(\tfrac13-\varepsilon,\tfrac13+\varepsilon\Big)\cap\Big(\tfrac14,\tfrac12\Big),
--   $$
--   such that
--   1. $\mathrm{LP}(J)=M$;
--   2. $M=O\big((\mathrm{LP}(I)+1)^4\big)$;
--   3. $$\mathrm{OPT}(I)-\mathrm{LP}(I)\ \le\ 3+96\,\big(\mathrm{OPT}(J)-\mathrm{LP}(J)\big).$$
--
--   So instances in which every bin holds at most three items, all of size arbitrarily close to $1/3$, already exhibit the additive configuration-LP gap of arbitrary bin packing instances, up to a constant factor and an additive constant.
--
--   **Formalization Note** Instances are raw lists of rational sizes $p/q$ with $0<p\le q$, read by the machine in the published binary encoding; the output is the pair $(M,J)$. The algorithm is one finite-alphabet Turing machine running in time polynomial in the input length, chosen after $\varepsilon$. The $O(\cdot)$ is one constant $C$, chosen after $\varepsilon$ and the algorithm, with $M\le C(\mathrm{LP}(I)+1)^4$ for every input $I$. All guarantees hold for every valid input, including the empty instance.
--
--   Differences from the source:
--   - reading: M = O((LP(I) + 1)⁴) → ∃ C (after ε and the algorithm), ∀ valid I, M ≤ C·(LP(I) + 1)⁴; reason: the uniform reading of O(·) in the instance; the proof gives explicit bounds m ≤ B(B+1), B < L + 3/2, |V| ≤ m + B + |H|, |H| ≤ m² + 1
--   - encoding: a polynomial-time algorithm on bin packing instances → a Mathlib TM2ComputableInPolyTime machine with a finite alphabet from rawInstanceBits to rawReductionOutputBits, guarantees on valid raw inputs; reason: the published encoding of instances and reductions, as in OAI.BinPackingGap and Theorem 1.1
--   - encoding: rational sizes in an open interval with real ε → sizes cast to ℝ and compared with the real ε; reason: same instances
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Theorem 1.2, p.2 (proof §2.3, pp.9–11)

import Mathlib
import Definitions.Def_BinPackingGap

namespace LogStarBinPacking.Supplement

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Theorem 1.2 (universal three-item reduction preserving the configuration-LP gap).**
Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript
(sha256 1d88425d…), Theorem 1.2, p.2.
For every `ε > 0` there is a polynomial-time algorithm which, given any bin packing instance `I`,
produces a bin packing instance `J` of `3M` items, where `M ≥ 1` is an integer, with sizes in
`(1/3 − ε, 1/3 + ε) ∩ (1/4, 1/2)` such that `LP(J) = M = O((LP(I) + 1)⁴)` and
`OPT(I) − LP(I) ≤ 3 + 96(OPT(J) − LP(J))`.

**Formalization Note** An input instance is a raw list of sizes `p/q` (`RawInstance`, valid when
`0 < p ≤ q`), given to the machine in the published binary encoding `rawInstanceBits`; the output
is the pair `(M, J)` with `J` raw, encoded by `rawReductionOutputBits`. The algorithm is one Mathlib
`TM2ComputableInPolyTime` machine with a finite alphabet, chosen after `ε` (it may depend on `ε`);
its guarantees are required on every valid input, including the empty instance. `O((LP(I)+1)⁴)` is
read as: one constant `C`, chosen after `ε` and the algorithm and independent of `I`, with
`M ≤ C (LP(I)+1)⁴` for every valid `I`. `LP` is the published configuration LP `individualLP` and
`OPT` the published `opt`; the gap inequality is stated in `ℝ`. Sizes are rational and compared with
the real `ε` in `ℝ`. -/
theorem theorem_1_2 :
    ∀ ε : ℝ, 0 < ε →
      ∃ reduce : RawInstance → RawReductionOutput,
      ∃ comp : Turing.TM2ComputableInPolyTime BinaryEncoding.rawInstanceBits
          BinaryEncoding.rawReductionOutputBits reduce,
        MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
        ∃ C : ℝ, ∀ (r : RawInstance) (hr : r.Valid), ∃ hv : (reduce r).2.Valid,
          1 ≤ (reduce r).1 ∧
          (reduce r).2.length = 3 * (reduce r).1 ∧
          (∀ i : ((reduce r).2.toInstance hv).Item,
            1 / 3 - ε < ((((reduce r).2.toInstance hv).size i : ℚ) : ℝ) ∧
            ((((reduce r).2.toInstance hv).size i : ℚ) : ℝ) < 1 / 3 + ε ∧
            1 / 4 < ((((reduce r).2.toInstance hv).size i : ℚ) : ℝ) ∧
            ((((reduce r).2.toInstance hv).size i : ℚ) : ℝ) < 1 / 2) ∧
          individualLP ((reduce r).2.toInstance hv) = ((reduce r).1 : ℝ) ∧
          ((reduce r).1 : ℝ) ≤ C * (individualLP (r.toInstance hr) + 1) ^ 4 ∧
          (opt (r.toInstance hr) : ℝ) - individualLP (r.toInstance hr) ≤
            3 + 96 * ((opt ((reduce r).2.toInstance hv) : ℝ) -
              individualLP ((reduce r).2.toInstance hv)) := by sorry

end LogStarBinPacking.Supplement
