-- Prove2me | Theorems.Thm_NonmonotoneSubmod_RandomSet_Supplement_lemma_4_2
-- name    : NonmonotoneSubmod.RandomSet.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:17:24.365208+00:00
-- url     : https://prove2.me/theorems/4925b472-3905-484c-9b90-f55b9cb2b325
-- title:
--   Lemma 4.2 — the PSD weighted parity gap is NP-hard
-- statement:
--   Fix any real $\varepsilon>0$. Consider normalized finite rational-weight systems of Boolean parity equations, each with one variable in $X$ and two ordered variables in $Y$, with arbitrary right-hand parity bits. Let $W(a,b)$ be the satisfied weight, and let $P_{jk}$ be the total weight of equations whose ordered $Y$ positions are $j,k$. Even when the real matrix $P$ is positive semidefinite, the promise problem with classes
--   $$\mathrm{YES}:\quad\exists a,b,\ W(a,b)\ge1-\varepsilon,\qquad
--   \mathrm{NO}:\quad\forall a,b,\ W(a,b)\le\frac12+\varepsilon$$
--   is NP-hard under deterministic polynomial-time reductions. Precisely, every NP language over every finite nonempty alphabet has such a reduction sending members into YES and nonmembers into NO.
--
--   This is the full supporting hardness result for Theorem 4.3, including the PSD promise. It does not assume Håstad's verifier theorem or replace hardness by a Fourier inequality.
--
--   **Formalization Note** The two thresholds are disjoint for $0<\varepsilon<1/4$. For $\varepsilon\ge1/4$, they overlap: the two equations $x\oplus y\oplus y=0,1$ of weights $3/4,1/4$ have $P=[1]$ and optimum $3/4$, belonging to both classes. Consequently a classifier correct on both classes is impossible there. The reduction statement nevertheless retains the printed quantifier over every positive slack and demands genuine NP reductions throughout the disjoint range. PSD is real Hermitian symmetry together with a nonnegative quadratic form, not entrywise nonnegativity.
--
--   Differences from the source:
--   - generalization: weighted Boolean systems of total weight one → NP-hardness already on rational-weight encoded systems with the same total weight; reason: the PCP test distribution in the source is finite with rational probabilities; reductions into this subclass also prove hardness of the full source class
--   - encoding: NP-hard to distinguish the two thresholds for any fixed positive epsilon → every NP language admits an actual polynomial-time promise reduction, preserving both thresholds for every epsilon > 0; reason: the published promise-hardness definition imposes the two membership implications without assuming the thresholds disjoint; its nontrivial disjoint range 0 < epsilon < 1/4 remains fully required
--   - encoding: one X variable and ordered Y variables, with a positive semidefinite ordered-pair weight matrix → Fin-labelled disjoint X and Y types, explicit RHS bits and rational weights, and Matrix.PosSemidef of the real ordered-pair matrix; reason: finite labels change no system; repeated Y positions are allowed by the source; real PSD includes symmetry and every real quadratic-form test
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4):1133–1153, 2011, DOI 10.1137/090779346; p. 1145, Lemma 4.2

import Mathlib
import Definitions.Def_MeanBudgetXC_Supplement_PromiseNPHard
import Definitions.Def_NonmonotoneSubmod_RandomSet_Supplement_Parity

namespace NonmonotoneSubmod.RandomSet.Supplement

theorem lemma_4_2 (ε : ℝ) (hε : 0 < ε) :
    MeanBudgetXC.Supplement.PromiseNPHard (parityYes ε) (parityNo ε) := by sorry

end NonmonotoneSubmod.RandomSet.Supplement
