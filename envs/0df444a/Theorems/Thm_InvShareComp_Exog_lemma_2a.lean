-- Prove2me | Theorems.Thm_InvShareComp_Exog_lemma_2a
-- name    : InvShareComp.Exog.lemma_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:02.846458+00:00
-- url     : https://prove2.me/theorems/2ab78fcd-dd3b-4144-af95-6e57b160a4d8
-- title:
--   Lemma 2(a), p. 12 (PDF 12) — without sharing, (s, s) is a symmetric equilibrium iff s = ŝᴺ(I)
-- statement:
--   Consider the model under its standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density, symmetric exogenous inventories $I_1=I_2=I\in[0,1]$ and no sharing agreement. Then $(s,s)$ is a symmetric equilibrium of the service game if and only if
--   $$s=\hat s^N(I)=\frac{\beta\bigl(p\mu-\bar c\int_{2I}^1\varepsilon g(\varepsilon)\,d\varepsilon\bigr)}{2k}.$$
--
--   This is the paper's existence and uniqueness of the no-sharing equilibrium (equation (2)); it identifies the benchmark against which sharing is compared in Proposition 2.
--
--   **Formalization Note.** Deviations are restricted to those that keep both deterministic demands non-negative (p. 7). $\int_{2I}^1\varepsilon g(\varepsilon)\,d\varepsilon$ is $E[\varepsilon_1;\varepsilon_1\ge 2I]$. The bound $\beta\le\bar\beta$ of (A.7) is not assumed.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), p. 12 (PDF 12), Lemma 2(a), equation (2); proof in Online Appendix p. 6 (PDF 38)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem lemma_2a (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1) (s : ℝ) :
    IsSymEqNoShare P ν I s ↔ s = sHatN P ν I := by sorry

end InvShareComp.Exog
