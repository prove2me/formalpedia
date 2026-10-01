-- Prove2me | Theorems.Thm_MongeKantorovichYao_cConjugate_cConjugate_of_isCConcave
-- name    : MongeKantorovichYao.cConjugate_cConjugate_of_isCConcave
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T20:27:14.42972+00:00
-- url     : https://prove2.me/theorems/aa2e41c2-bca5-4f02-a151-3e2baf195844
-- title:
--   Theorem 4.25 — $(\psi^c)^c=\psi$ for $c$-concave $\psi$
-- statement:
--   Let $X,Y$ be sets and $c : X\times Y\to\mathbb R$. If $\psi : X\to\mathbb R$ is $c$-concave, then its double $c$-conjugate is $\psi$ itself:
--   $$(\psi^c)^c(x)=\inf_{y\in Y}\Big(c(x,y)-\inf_{x'\in X}\big(c(x',y)-\psi(x')\big)\Big)=\psi(x)\qquad\text{for all }x\in X.$$
--
--   This is used to show that the dual potentials $\psi$ and $\varphi=\psi^c$ determine each other, which gives their boundedness in the proof of Proposition 4.31.
--
--   **Formalization Note** Both conjugates are computed in the extended reals.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), p. 15, Theorem 4.25 (proof referred to Appendix A.4, p. 26)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs

open MeasureTheory

namespace MongeKantorovichYao

theorem cConjugate_cConjugate_of_isCConcave {X Y : Type*}
    (c : X × Y → ℝ) (ψ : X → ℝ) (hψ : IsCConcave c ψ) :
    cConjugate' c (cConjugate c (fun x => (ψ x : EReal))) = fun x => (ψ x : EReal) := by sorry

end MongeKantorovichYao
