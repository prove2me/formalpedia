-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_15
-- name    : MultiOmniRate.Lipschitz.lemma_3_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:31.543353+00:00
-- url     : https://prove2.me/theorems/39df1f1b-e5cb-4ff3-b23f-e600a4ca825b
-- title:
--   Lemma 3.15 — $\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H$ has a uniform $u$-cover inside the class with $\log(2|\mathcal B|)\le C_Ku^{-(K-1)}+\log(2N)$
-- statement:
--   Let $K\ge2$ and let $\mathcal H$ be a class of $N\ge1$ hypotheses $\mathcal X\to\Delta_K$. There is $C_K$, depending only on $K$, such that for every $0<u\le1$ there is a uniform $u$-cover $\mathcal B\subseteq\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H$ of $\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H=\{x\mapsto\Delta\ell(h(x)):\ell\in\mathcal L_{\mathrm{Lip}},h\in\mathcal H\}$ with
--   $$\log(2|\mathcal B|)\le C_Ku^{-(K-1)}+\log(2N).$$
--
--   This is the covering bound behind the hypothesis learner for Lipschitz losses (Algorithm 4).
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: a class $\mathcal H$ of $N$ hypotheses → a family $h:\mathrm{Fin}\,N\to(\mathcal X\to\Delta_K)$ and $\mathcal H$ its range (repetitions allowed); reason: a class of at most $N$ hypotheses; the bound is monotone in $N$
--   - encoding: $\ell\in\mathcal L_{\mathrm{Lip}}$ in $\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H$ → pairs $(\ell,\mathrm{BR}_\ell)$ of `LLip K`; the test $x\mapsto\Delta\ell(h(x))$ uses $\ell$ only; reason: every Lipschitz loss has a measurable best response, so the class of tests is the same
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 36, Lemma 3.15

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_15 : ∀ (K : ℕ) [NeZero K], 2 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type*) (N : ℕ), 1 ≤ N → ∀ (h : Fin N → X → Simplex K) (u : ℝ),
      0 < u → u ≤ 1 →
      ∃ B : Finset (X → Fin K → ℝ),
        (↑B : Set (X → Fin K → ℝ)) ⊆ testClass (LLip K) (Set.range h) ∧
        IsUniformCover B (testClass (LLip K) (Set.range h)) u ∧
        Real.log (2 * (B.card : ℝ)) ≤ C * u ^ (-((K : ℝ) - 1)) + Real.log (2 * N) := by sorry

end MultiOmniRate.Lipschitz
