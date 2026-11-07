-- Prove2me | Theorems.Thm_MinSumClust_theorem_2
-- name    : MinSumClust.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:40.268936+00:00
-- url     : https://prove2.me/theorems/840ed572-8223-4ff9-9e49-061e85c5db70
-- title:
--   Theorem 2 — a polynomial-time LMP algorithm: $f|\mathcal S|+\mathrm{cost}(\mathcal S)\le k f+2\times10^7\,\mathrm{opt}$
-- statement:
--   There is a polynomial-time algorithm that, given a well-formed min-sum $k$-clustering instance and a rational $f>0$, outputs a clustering $\mathcal S$ of the clients (a labelling of length $n$) with
--
--   $$f\,|\mathcal S|+\mathrm{cost}(\mathcal S)\ \le\ k\cdot f+2\times 10^{7}\cdot\mathrm{opt}.$$
--
--   Here $|\mathcal S|$ is the number of clusters, the cost counts ordered pairs, and $\mathrm{opt}$ is the optimal cost of a partition into exactly $k$ nonempty clusters. This Lagrangian-multiplier-preserving guarantee is the first half of the proof of Theorem 1.
--
--   Differences from the source:
--
--   - reading: a polynomial-time algorithm taking an instance and f > 0 → a Mathlib Turing.TM2ComputableInPolyTime machine from encInstF (instance and rational f, in binary) to encLabels; reason: the paper names no machine model; an input f must be finitely representable
--   - encoding: a clustering 𝒮 with |𝒮| clusters → a labelling of the n clients, |𝒮| = number of distinct labels; rational distances; ordered-pair cost; malformed inputs get any output; reason: Lean convention; every clustering is the label classes of some labelling
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Theorem 2, p.4 (PDF p.6); restated p.19 (PDF p.21); proof p.25

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_MinSumClust_Inst
import Definitions.Def_MinSumClust_opt
import Definitions.Def_MinSumClust_encInst

namespace MinSumClust

/-- **Theorem 2 (LMP approximation)**, p.4 (PDF p.6); restated p.19 (PDF p.21).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Theorem 2, p.4.

There is a polynomial-time algorithm that, given a min-sum k-clustering instance and `f > 0`,
outputs a clustering `𝒮` with `f|𝒮| + cost(𝒮) ≤ k · f + 2 × 10⁷ · opt`.

**Formalization Note.** "Polynomial-time algorithm" is a Mathlib `Turing.TM2ComputableInPolyTime`
machine from the encoding `encInstF` of `(instance, f)` to the encoding `encLabels` of a labelling;
`f` is a rational input. The output is a labelling of the `n` clients; its clusters are the label
classes, `|𝒮|` is the number of distinct labels and the cost counts ordered pairs. The guarantee is
for well-formed instances; malformed inputs may get any output. -/
theorem theorem_2 :
    ∃ alg : Inst × ℚ → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encInstF encLabels alg) ∧
      ∀ I : Inst, I.WellFormed → ∀ f : ℚ, 0 < f →
        (alg (I, f)).length = I.n ∧
          (f : ℝ) * numClusters (alg (I, f)) + labelCost I (alg (I, f)) ≤
            I.k * (f : ℝ) + 20000000 * opt I := by sorry

end MinSumClust
