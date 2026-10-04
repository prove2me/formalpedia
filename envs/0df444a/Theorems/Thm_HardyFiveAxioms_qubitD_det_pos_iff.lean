-- Prove2me | Theorems.Thm_HardyFiveAxioms_qubitD_det_pos_iff
-- name    : HardyFiveAxioms.qubitD_det_pos_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T23:05:19.996204+00:00
-- url     : https://prove2.me/theorems/69c1c573-1713-4f8d-a8a0-4672bffea9ac
-- title:
--   Qubit: $\det D>0\iff c_-<c<c_+$
-- statement:
--   Let $0\le a,b\le1$ and $c\in\mathbb R$, and let $D=D(a,b,c)$ be the $4\times4$ matrix of Eq. (34)/(74). Then
--
--   $$\det D>0\iff c_-<c<c_+,\qquad c_\pm=1-a-b+2ab\pm2\sqrt{ab(1-a)(1-b)} .$$
--
--   In Section 5 Hardy observes that the quantum constraint $c_-<c<c_+$ (Eqs. (36)–(37)) "is equivalent to the condition $\mathrm{Det}(D)>0$". In Section 8.6 he notes that $\det D=0$ has the same roots $c_\pm$ as $\det A=0$.
--
--   **Formalization Note** At the boundary $a\in\{0,1\}$ or $b\in\{0,1\}$ one has $c_-=c_+$, so the interval is empty and $\det D\le0$.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 9, Section 5, Eqs. (34), (36)–(37) and the sentence after (37); p. 21, Section 8.6, after Eq. (85)

import Mathlib
import Definitions.Def_hardy2001_qubit

namespace HardyFiveAxioms

/-- Hardy 2001, Section 5, Eqs. (36)–(37) (and Section 8.6, Eq. (85)): for `0 ≤ a, b ≤ 1`,
`det D > 0` if and only if `c₋ < c < c₊`. -/
theorem qubitD_det_pos_iff (a b c : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    0 < (qubitD a b c).det ↔ cMinus a b < c ∧ c < cPlus a b := by sorry

end HardyFiveAxioms
