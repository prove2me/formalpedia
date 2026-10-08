-- Prove2me | Theorems.Thm_OCB2012_isCausallySeparable_of_isDiag
-- name    : OCB2012.isCausallySeparable_of_isDiag
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-07T23:11:25.356877+00:00
-- url     : https://prove2.me/theorems/5eefb2f1-2b88-4845-adf5-d4a626bf11a3
-- title:
--   Appendix F — classical (diagonal) processes are causally separable
-- statement:
--   Throughout, $A_1,A_2$ (Alice's input and output) and $B_1,B_2$ (Bob's) are finite-dimensional systems; operators on $A_1A_2B_1B_2$ are complex matrices in that tensor order. A CJ matrix $M^{X_1X_2}$ of a CPTP map satisfies $M\ge 0$ and $\operatorname{Tr}_{X_2}M=\mathbb 1^{X_1}$. Every process matrix $W$ that is diagonal in the product basis $\{|i\rangle^{A_1}|j\rangle^{A_2}|k\rangle^{B_1}|l\rangle^{B_2}\}$ (a classical process) is causally separable: $W=q\,W^{B\not\preceq A}+(1-q)\,W^{A\not\preceq B}$ for some $q\in[0,1]$ and process matrices $W^{B\not\preceq A}=\mathbb 1^{B_2}\otimes W^{A_1A_2B_1}$, $W^{A\not\preceq B}=\mathbb 1^{A_2}\otimes W^{A_1B_1B_2}$. Dimensions are arbitrary.
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 5, section 'Classical processes are causally separable'; Appendix F, Eqs. (28)–(43)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem isCausallySeparable_of_isDiag {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (hW : IsProcessMatrix W) (hdiag : W.IsDiag) :
    IsCausallySeparable W := by sorry

end OCB2012
