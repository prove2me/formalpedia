-- Prove2me | Theorems.Thm_MemoryRegret_lemma_3_2_likelihood_ratio
-- name    : MemoryRegret.lemma_3_2_likelihood_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:39:21.357382+00:00
-- url     : https://prove2.me/theorems/51033e1a-c27f-4a7f-bf75-2b89711f8a85
-- title:
--   Lemma 3.2 — block likelihood ratio, YES against NO
-- statement:
--   Let $\varepsilon\in(0,\frac12)$, $C>2$, $m\in\mathbb N$, and let $P$ be a distribution on the class. Let $b'\in\{0,1\}^m$ have $m_0$ zeros with $|2m_0-m|<C\sqrt m$. Then for every $x$,
--   $$\Biggl|\frac{\mathbb E_{h\sim P}\Pr_{b\sim\mathrm{Ber}(h(x),\frac12+\varepsilon)^m}[b=b']}{\mathbb E_{b_0\in_R\{0,1\}}\Pr_{b\sim\mathrm{Ber}(b_0,\frac12+\varepsilon)^m}[b=b']}-1\Biggr|\le\alpha_x\cdot2C\varepsilon\sqrt m,\qquad\alpha_x=\bigl|\mathbb E_{h\sim P}[(-1)^{h(x)}]\bigr|.$$
--
--   This is the block-level analogue of the extractor property: a balanced block reveals little beyond what the bias $\alpha_x$ of $x$ under the current posterior allows.
--
--   **Formalization Note** The denominator is positive for $\varepsilon\in(0,\frac12)$, so the division is genuine.
--
--   Differences from the source:
--   - generalization: a distribution P over H ⊆ {0,1}^X → a probability vector P on the index type of a family hyp : ι → X → Bool; reason: ι = H with hyp h = h is the source statement; the family form allows repetitions
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Lemma 3.2, p.11

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_sgn
import Definitions.Def_MemoryRegret_berBlock

namespace MemoryRegret

/-- **Lemma 3.2 (block likelihood ratio, YES vs NO).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Lemma 3.2, p.11.

Let `ε ∈ (0, ½)`, `C > 2`, `m ∈ ℕ`, `(hyp i)_{i∈ι}` a class with a distribution `P` on `ι`, and
`b′ ∈ {0,1}^m` with `m₀` zeros and `|2m₀ − m| < C√m`. Then for every `x`,
`|E_{h∼P} Pr_{b∼Ber(h(x),½+ε)^m}[b = b′] / E_{b₀∈_R{0,1}} Pr_{b∼Ber(b₀,½+ε)^m}[b = b′] − 1|
  ≤ α_x · 2Cε√m`, where `α_x = |E_{h∼P}[(−1)^{h(x)}]|`.

**Formalization Note.** The class is an indexed family and `P` a probability vector on the
index type; a distribution on `H` is the same thing for an injective family. The denominator is
`blockLabelLaw ε b′ > 0` for `ε ∈ (0, ½)`, so the division is genuine. -/
theorem lemma_3_2_likelihood_ratio {X ι : Type} [Fintype ι] (hyp : ι → X → Bool)
    (P : ι → ℝ) (hP : IsProbVec P) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) (C : ℝ) (hC : 2 < C)
    (m : ℕ) (b' : Fin m → Bool) (hb' : |2 * (numZeros b' : ℝ) - m| < C * Real.sqrt m) (x : X) :
    |(∑ i, P i * berBlock ε (hyp i x) b') / blockLabelLaw ε b' - 1| ≤
      |∑ i, P i * sgn (hyp i x)| * (2 * C * ε * Real.sqrt m) := by sorry

end MemoryRegret
