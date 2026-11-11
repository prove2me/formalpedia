-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_theorem_2_2
-- name    : HopfieldPSpin.Shattering.theorem_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:09:56.624233+00:00
-- url     : https://prove2.me/theorems/e88ea19f-5b38-4e08-9196-2a6474a5530e
-- title:
--   Theorem 2.2 — shattering of the $p$-spin Hopfield Gibbs measure for $(1+\varepsilon)\sqrt{2\log p/p}\le\beta\le(1-\varepsilon)\sqrt{2\log2}$
-- statement:
--   Fix $\alpha\in(0,\infty)$ and $\varepsilon\in(0,1)$, and let $\delta=\varepsilon/4$,
--   $$r_p=\frac1{2p^{1+\delta}},\qquad R_p=\frac\delta{2p}=\frac\varepsilon{8p}.$$
--   There is $p_0=p_0(\alpha,\varepsilon)\in\mathbb N$ such that for every $p\ge p_0$, every storage sequence with $M_n/n^{p-1}\to\alpha$, either pattern law (i.i.d. $N(0,1)$ or i.i.d. Rademacher entries) and every inverse temperature
--   $$(1+\varepsilon)\sqrt{\frac{2\log p}p}\le\beta\le(1-\varepsilon)\sqrt{2\log2},$$
--   the Gibbs measures $(\mu_{n,\beta})_{n\ge1}$ are $(r_p,R_p)$-shattered: there are $c_1,c_2,c_3>0$, independent of $n$ and of the disorder, such that the probability over the patterns that $\mu_{n,\beta}$ is $(r_p,R_p,c)$-shattered (Definition 2.1(a): exponentially many disjoint nonempty clusters of Hamming diameter $\le r_pn$, pairwise separated by $\ge R_pn$, each of Gibbs mass $\le e^{-c_2n}$, together carrying mass $\ge1-e^{-c_3n}$) tends to $1$ as $n\to\infty$.
--
--   This is the paper's main shattering result; it holds for even and odd $p$ and both pattern laws.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - encoding: $\lim_n\mathbb P(S_n(r_p,R_p,c))=1$ → the outer measure of $\{\eta:\mu_{n,\beta}\text{ not }(r_p,R_p,c)\text{-shattered}\}$ tends to 0; reason: equivalent since $S_n$ is measurable; the complement form needs no measurability proof and is not weaker
--   - encoding: storage condition (2.2), $M_n/n^{p-1}\to\alpha$ → `StorageCondition p M α` (`Tendsto (M n / n^(p-1)) atTop (𝓝 α)`, natural exponent $p-1$); reason: same condition for $p\ge1$
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 6 (PDF 8), Theorem 2.2, (2.3)–(2.4); Definition 2.1 p. 5 (PDF 7); proof p. 36 (PDF 38)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model
import Definitions.Def_HopfieldPSpin_Shattering_Entropy
import Definitions.Def_HopfieldPSpin_Shattering_Shattered

open MeasureTheory Filter Topology

namespace HopfieldPSpin.Shattering

/-- Theorem 2.2 (p. 6), shattering in the Hopfield model: for `α > 0` and `ε ∈ (0, 1)` there
is `p₀(α, ε)` such that for every `p ≥ p₀`, every storage sequence with `M_n / n^{p−1} → α`,
either pattern law and every `β` with `(1 + ε)√(2 log p / p) ≤ β ≤ (1 − ε)√(2 log 2)`, there
are `c₁, c₂, c₃ > 0` (independent of `n` and of the disorder) such that the probability that
`µ_{n,β}` is `(r_p, R_p, c)`-shattered tends to one, `r_p = 1/(2 p^{1+ε/4})`, `R_p = ε/(8p)`. -/
theorem theorem_2_2 (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p → ∀ M : ℕ → ℕ, StorageCondition p M α →
      ∀ law : PatternLaw, ∀ β : ℝ,
        (1 + ε) * Real.sqrt (2 * Real.log p / p) ≤ β →
        β ≤ (1 - ε) * Real.sqrt (2 * Real.log 2) →
        ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
          Tendsto (fun n : ℕ => disorderLaw n (M n) law
              {η | ¬ IsShattered n (radiusR ε p) (radiusBigR ε p) c₁ c₂ c₃ (gibbs n (M n) p β η)})
            atTop (𝓝 0) := by sorry

end HopfieldPSpin.Shattering
