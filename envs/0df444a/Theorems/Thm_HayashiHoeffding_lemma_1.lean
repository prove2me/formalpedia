-- Prove2me | Theorems.Thm_HayashiHoeffding_lemma_1
-- name    : HayashiHoeffding.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:33.073618+00:00
-- url     : https://prove2.me/theorems/a21565a4-0436-46a2-84f3-2a90c0496ecd
-- title:
--   Lemma 1: $\operatorname{Tr}X^sY^{1-s}\ge\operatorname{Tr}\{X^{1-s}-Y^{1-s}\ge0\}Y+\operatorname{Tr}\{X^{1-s}-Y^{1-s}<0\}X$
-- statement:
--   Let $X$, $Y$ be positive trace-class operators on a complex Hilbert space $\mathcal H$ and $0 \le s \le 1/2$. Then
--
--   $$\operatorname{Tr} X^s Y^{1-s} \;\ge\; \operatorname{Tr}\,\{X^{1-s} - Y^{1-s} \ge 0\}\, Y + \operatorname{Tr}\,\{X^{1-s} - Y^{1-s} < 0\}\, X ,$$
--
--   where for a self-adjoint $C$ with spectral decomposition $C = \sum_i c_i E_i$, $\{C \ge 0\} = \sum_{c_i \ge 0} E_i$ and $\{C < 0\} = \sum_{c_i < 0} E_i$.
--
--   Applied to $X = \sigma^{\otimes n} e^{-na}$, $Y = \rho^{\otimes n}$ it bounds both error probabilities of the test $\{X^{1-s} - Y^{1-s} < 0\}$ at once (eqs. (6)–(7)).
--
--   **Formalization Note** The projections are `nonnegProj` and `negProj`; powers are `qPow` ($X^0$ is the support projection of $X$); the inequality is in $\mathbb C$ with `ComplexOrder`.
--
--   Differences from the source:
--   - reading: "positive-semidefinite operators X, Y" → positive trace-class operators; reason: in infinite dimension the traces in the display must exist; the paper's $X$, $Y$ are $\sigma^{\otimes n}e^{-na}$ and $\rho^{\otimes n}$, which are trace class.
--   - reading: $X^0$ at $s = 0$ (undefined on the page for singular $X$) → the support projection $\Pi_X$; reason: the limit of $X^s$ as $s \to 0^+$; it is the stronger reading.
--   - reading: the sentence "we define the projection P as the projection on the range of $X^{1-s} - Y^{1-s}$" → omitted; reason: $P$ does not occur in the displayed inequality.
--   - encoding: $\{C \ge 0\}$, $\{C < 0\}$ via a discrete spectral decomposition → $I - \Pi_{C_-}$ and $\Pi_{C_-}$ (support projection of the negative part); reason: Mathlib has no Borel functional calculus; these are the spectral projections of $[0,\infty)$ and $(-\infty,0)$ for every self-adjoint $C$.
--   - encoding: the inequality between traces → the partial order of $\mathbb C$; reason: it asserts that the difference is real and nonnegative, as meant on the page.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, Lemma 1, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
import Definitions.Def_HayashiHoeffding_negProj
import Definitions.Def_HayashiHoeffding_nonnegProj

open QAlgorithms.Papers.Independent.Next46.P02 QChernoff.Trace
open scoped ComplexOrder

namespace HayashiHoeffding

universe u

/-- **Lemma 1.** For positive trace-class operators `X, Y` on a complex Hilbert space and
`0 ≤ s ≤ 1/2`,
`Tr X^s Y^{1−s} ≥ Tr {X^{1−s} − Y^{1−s} ≥ 0} Y + Tr {X^{1−s} − Y^{1−s} < 0} X`.

Hayashi, arXiv:quant-ph/0611013v2, Lemma 1, p.3.

**Formalization Note.**
1. `{C ≥ 0}` and `{C < 0}` are `nonnegProj C` and `negProj C` (spectral projections of
   `[0, ∞)` and `(−∞, 0)`, through the support projection of `C⁻`).
2. Powers are `qPow`; at `s = 0` the factor `X^0` is the support projection `Π_X`.
3. `X, Y` are assumed trace class (the paper's `X, Y` are `σ^{⊗n} e^{−na}` and `ρ^{⊗n}`), so
   every trace in the display exists.
4. The projection `P` named in the lemma's first sentence is not used by the display and is
   omitted.
5. The inequality is in `ℂ` with `ComplexOrder` (it also asserts that the difference is real). -/
theorem lemma_1 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X Y : H →L[ℂ] H) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXtc : IsModulusTraceClass X) (hYtc : IsModulusTraceClass Y)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    basisOperatorTrace (nonnegProj (qPow X (1 - s) - qPow Y (1 - s)) * Y) +
        basisOperatorTrace (negProj (qPow X (1 - s) - qPow Y (1 - s)) * X) ≤
      basisOperatorTrace (qPow X s * qPow Y (1 - s)) := by sorry

end HayashiHoeffding
