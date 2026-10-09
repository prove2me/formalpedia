-- Prove2me | Theorems.Thm_OCB2012_W7_not_causallySeparable
-- name    : OCB2012.W7_not_causallySeparable
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-07T23:10:43.185598+00:00
-- url     : https://prove2.me/theorems/5590a4b9-7f9f-42c0-a9d9-ea55c62c5e88
-- title:
--   p. 5 — the process matrix of Eq. (7) is not causally separable
-- statement:
--   The four-qubit process matrix $W$ of Eq. (7) is **not causally separable**: there are no $q\in[0,1]$ and process matrices $W^{B\not\preceq A}=\mathbb 1^{B_2}\otimes W^{A_1A_2B_1}$, $W^{A\not\preceq B}=\mathbb 1^{A_2}\otimes W^{A_1B_1B_2}$ with $W=q\,W^{B\not\preceq A}+(1-q)\,W^{A\not\preceq B}$.
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 5, sentence after Eq. (8): 'which proves that (7) is not causally separable'; Eq. (6)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem W7_not_causallySeparable : ¬ IsCausallySeparable W7 := by sorry

end OCB2012
