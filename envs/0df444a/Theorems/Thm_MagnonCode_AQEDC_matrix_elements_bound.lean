-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_matrix_elements_bound
-- name    : MagnonCode.AQEDC.matrix_elements_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:04.498415+00:00
-- url     : https://prove2.me/theorems/ae67ded8-4f7b-428f-aaec-4589d9d631a5
-- title:
--   §7.8, display on p. 70: the Knill-Laflamme type bound for magnon-states
-- statement:
--   There is an absolute constant $C>0$ such that for $s_0\le n-2$, for all $r,s\le s_0$, every set $A$ of sites and every $F$ acting on $A$ with $\|F\|\le1$,
--
--   $$
--   \bigl|\langle\psi_r|F|\psi_s\rangle-\delta_{r,s}\langle\psi_0|F|\psi_0\rangle\bigr|\le C\sqrt{\frac{|A|\,s_0}{n}}.
--   $$
--
--   With $s_0$ of order $n^\kappa$ and $|A|\le d$ this is the printed $O(d^{1/2}n^{(\kappa-1)/2})$. It is the hypothesis (8) of Corollary 3.4 for the magnon code.
--
--   Differences from the source:
--   - generalization: r, s even with r, s ≤ 2n^κ; F d-local → any s₀ ≤ n − 2 and r, s ≤ s₀, not necessarily even; F acting on any A; reason: s₀ of order 2n^κ and |A| ≤ d specialize to the source
--   - encoding: O(d^{1/2} n^{(κ−1)/2}) → C √(|A| s₀/n) with C > 0 before all other data; reason: √(d·2n^κ/n) is √2 times the printed rate
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, §7.8, proof of Theorem 7.9, display on p. 70

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_psiNorm
import Definitions.Def_MagnonCode_AQEDC_IsLocalOn

open scoped Matrix Matrix.Norms.L2Operator

namespace MagnonCode.AQEDC

/-- **Display in the proof of Theorem 7.9** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, §7.8, p. 70): there is an absolute `C` such that
for `s₀ ≤ n − 2`, `r, s ≤ s₀`, every set `A` of sites and every `F` acting on `A` with `‖F‖ ≤ 1`,
`|⟨ψ_r|F|ψ_s⟩ − δ_{r,s}⟨ψ_0|F|ψ_0⟩| ≤ C √(|A| s₀ / n)`.

**Formalization Note** The printed display is the case `s₀ = 2n^κ`, `|A| = d`, `r, s` even, where
`√(d s₀ / n)` is a constant times `d^{1/2} n^{(κ−1)/2}`. -/
theorem matrix_elements_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n s₀ r s : ℕ, s₀ + 2 ≤ n → r ≤ s₀ → s ≤ s₀ →
      ∀ (A : Finset (Fin n)) (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
        IsLocalOn A F → ‖F‖ ≤ 1 →
          ‖star (psiNorm n r) ⬝ᵥ F *ᵥ psiNorm n s -
              (if r = s then star (psiNorm n 0) ⬝ᵥ F *ᵥ psiNorm n 0 else 0)‖ ≤
            C * Real.sqrt ((A.card : ℝ) * (s₀ : ℝ) / (n : ℝ)) := by sorry

end MagnonCode.AQEDC
