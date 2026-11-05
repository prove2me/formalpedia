-- Prove2me | Theorems.Thm_MagnonCode_AQEDC_theorem_7_8
-- name    : MagnonCode.AQEDC.theorem_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:51.623668+00:00
-- url     : https://prove2.me/theorems/a9bdb053-b1c6-4f64-b449-5529379defda
-- title:
--   Theorem 7.8, any support: diagonal matrix elements nearly agree
-- statement:
--   There is an absolute constant $C>0$ such that for $s_0\le n-2$, for all $r,s\le s_0$, every set $A$ of sites and every $F$ acting on $A$ with $\|F\|\le1$,
--
--   $$
--   \bigl|\langle\psi_s|F|\psi_s\rangle-\langle\psi_r|F|\psi_r\rangle\bigr|\le C\sqrt{\frac{|A|\,s_0}{n}}.
--   $$
--
--   Local observables thus cannot tell the magnon-states apart.
--
--   Differences from the source:
--   - generalization: F acting on the first d sites → F acting on any set A of sites; reason: Lemma 7.4 is false, so Theorem 7.9 needs arbitrary supports; A = first d sites specializes to the source
--   - encoding: O(√(d s₀/n)) → ∃ C > 0 before all other data, with |A| for d; reason: the O(·) is uniform in n, d, s₀, r, s and F, as the proof of Theorem 7.9 uses it
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Theorem 7.8, p. 69

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_psiNorm
import Definitions.Def_MagnonCode_AQEDC_IsLocalOn

open scoped Matrix Matrix.Norms.L2Operator

namespace MagnonCode.AQEDC

/-- **Theorem 7.8, any support** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 69): there is an absolute `C` such that for `s₀ ≤ n − 2`,
`r, s ≤ s₀`, every set `A` of sites and every `F` acting on `A` with `‖F‖ ≤ 1`,
`|⟨ψ_s|F|ψ_s⟩ − ⟨ψ_r|F|ψ_r⟩| ≤ C √(|A| s₀ / n)`.

**Formalization Note** `O(·)` is an absolute constant preceding all data, and `|A|` is the printed
`d`. Printed for the first `d` sites; the reduction to that case (Lemma 7.4) is false, so `A` is
arbitrary. -/
theorem theorem_7_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ n s₀ r s : ℕ, s₀ + 2 ≤ n → r ≤ s₀ → s ≤ s₀ →
      ∀ (A : Finset (Fin n)) (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
        IsLocalOn A F → ‖F‖ ≤ 1 →
          ‖star (psiNorm n s) ⬝ᵥ F *ᵥ psiNorm n s - star (psiNorm n r) ⬝ᵥ F *ᵥ psiNorm n r‖ ≤
            C * Real.sqrt ((A.card : ℝ) * (s₀ : ℝ) / (n : ℝ)) := by sorry

end MagnonCode.AQEDC
