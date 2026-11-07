-- Prove2me | Theorems.Thm_MeanBudgetXC_eq_14
-- name    : MeanBudgetXC.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:47.792079+00:00
-- url     : https://prove2.me/theorems/cedde1d9-05da-4ce6-a004-784c6bec7416
-- title:
--   Eq. (14) — the coefficient bodies are antiblockers
-- statement:
--   Let $d\le N$, let $Q$ be a graph on the vertex set, and let $C_Q=\ \downarrow\mathrm{conv}\{c_S:|S|=d\}$. Then the antiblocker of $C_Q$ is $Z_Q$, we have $C_Q=\mathrm{abl}(Z_Q)$, and for $B>0$,
--   $$\mathrm{abl}(Z_{Q,B})=\ \downarrow\mathrm{conv}\big(C_Q\cup\{(2/B)\mathbf 1_E\}\big)=C_{Q,B}.$$
--
--   These identities turn a formulation of the pair body into a formulation of the coefficient body, on which the combinatorial argument runs.
--
--   Differences from the source:
--   - generalization: $Q$ is triangle-free with $\Delta(Q)\le d-1$ and $3\le d\le N$, the setting of Lemma 4.1 → $Q$ is any graph and $d\le N$; reason: the identities concern the bodies as defined by (11), (12) and before (14), and never use those conditions; the paper's setting is a special case
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.1, display (14) and the sentences before it, p.18

import Mathlib
import Definitions.Def_MeanBudgetXC_abl
import Definitions.Def_MeanBudgetXC_budgetZeroSection
import Definitions.Def_MeanBudgetXC_budgetCoeffBody

namespace MeanBudgetXC

/-- **Display (14)** and the antiblocker identities before it (Chao–Gao–Qi–Wang, *A Sharp
Mean-Budget Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256
882d9c71…9e76, Section 4.1, p.18). Let `C_Q = ↓conv{c_S : |S| = d}`. Its antiblocker is `Z_Q`;
`C_Q = abl(Z_Q)`; and for `B > 0`,
`abl(Z_{Q,B}) = ↓conv(C_Q ∪ {(2/B) 1_E}) =: C_{Q,B}`.

**Formalization Note** The graph `Q` on the finite vertex type `V` (`N = card V`) is arbitrary
and `d ≤ N` (so that `d`-sets exist): the identities concern the bodies `Z_Q`, `C_Q` as defined by
(11) and before (14), and need neither triangle-freeness nor the degree bound of Lemma 4.1. -/
theorem eq_14 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hdN : d ≤ Fintype.card V)
    (Q : SimpleGraph V) [DecidableRel Q.Adj] :
    abl (coeffBody Q d) = zeroSection Q d ∧ coeffBody Q d = abl (zeroSection Q d) ∧
      ∀ B : ℝ, 0 < B → abl (budgetZeroSection Q d B) = budgetCoeffBody Q d B := by sorry

end MeanBudgetXC
