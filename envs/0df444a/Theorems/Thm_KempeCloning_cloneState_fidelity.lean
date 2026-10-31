-- Prove2me | Theorems.Thm_KempeCloning_cloneState_fidelity
-- name    : KempeCloning.cloneState_fidelity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:06.705109+00:00
-- url     : https://prove2.me/theorems/1706b1f3-30b7-4017-a579-6eaa08045eb5
-- title:
--   Eq. (20): the fidelity of $|\mathcal F_l\rangle$ is $\frac{m(m+2)+l(m+1)}{(m+l)(m+2)}$
-- statement:
--   Let $m, N\in\mathbb N$ and $0\le l\le N$ with $m + l\ge 1$, and let $|\mathcal F_l\rangle$ be the state (19). The fidelity of the cloning, the mean relative frequency of photons in the correct mode $a_1$ in $|\mathcal F_l\rangle$, is
--
--   $$F_l = \binom{m+l+1}{l}^{-1}\sum_{i=0}^{l}\binom{m+l-i}{m}\frac{m+l-i}{m+l} = \frac{m(m+2)+l(m+1)}{(m+l)(m+2)} .$$
--
--   This is the fidelity of the optimal universal $m\to m+l$ cloner; the optimality of that value is a result the paper cites and is not part of this statement.
--
--   Differences from the source:
--   - encoding: the fraction $(m+l-i)/(m+l)$, undefined at $m+l=0$ → hypothesis $0 < m+l$; reason: excludes only the case in which the page's fraction is $0/0$
--   - encoding: fidelity "given by the mean relative frequency of photons in the correct mode" → $\sum_n |\psi(n)|^2\, n_{a_1}/(n_{a_1}+n_{a_2})$; reason: the page's notion written out; $|\mathcal F_l\rangle$ is normalized, so no division by the norm is needed
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, (20), p.5

import Definitions.Def_KempeCloning_cloneState
import Definitions.Def_KempeCloning_relFreqA1

namespace KempeCloning

/-- **The cloning fidelity (20) of `|F_l⟩`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, (20), p.5: "let us calculate the
fidelity of the cloning, given by the mean relative frequency of photons in the correct mode (a1 in
our case). In the state |m + l − i, i⟩photons the relative frequency of correct photons is
(m + l − i)/(m + l). Therefore
F_l = binom(m+l+1, l)^{−1} Σ_{i=0}^{l} binom(m+l−i, m) (m+l−i)/(m+l) = (m(m+2) + l(m+1))/((m+l)(m+2))."

For all `m, N` and every `l ≤ N` with `m + l ≥ 1`, the mean relative frequency of photons in mode
`a₁` in `|F_l⟩` equals both expressions of (20). -/
theorem cloneState_fidelity (m N l : ℕ) (hl : l ≤ N) (hml : 0 < m + l) :
    relFreqA1 (cloneState m N l) =
        ((m + l + 1).choose l : ℝ)⁻¹ *
          ∑ i ∈ Finset.range (l + 1),
            ((m + l - i).choose m : ℝ) * (((m + l - i : ℕ) : ℝ) / ((m : ℝ) + l)) ∧
      relFreqA1 (cloneState m N l) =
        ((m : ℝ) * (m + 2) + l * (m + 1)) / (((m : ℝ) + l) * (m + 2)) := by sorry

end KempeCloning
