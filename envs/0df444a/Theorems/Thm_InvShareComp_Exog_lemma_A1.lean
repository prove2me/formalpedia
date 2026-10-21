-- Prove2me | Theorems.Thm_InvShareComp_Exog_lemma_A1
-- name    : InvShareComp.Exog.lemma_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:01.470449+00:00
-- url     : https://prove2.me/theorems/8536edea-3f17-4f04-b0fb-85c0e8c29f0f
-- title:
--   Lemma A.1(a)–(b), Online Appendix p. 2 (PDF 34) — exchanging the demand factors maps the sharing regions onto each other
-- statement:
--   Let $(\varepsilon_1,\varepsilon_2)$ have an exchangeable law $\nu$ on $[0,1]^2$ with a density, let $I\in[0,1]$, and let $Z:\mathbb R^2\to\mathbb R$ be any function. Then
--
--   1. $$E\bigl[Z(\varepsilon_1,\varepsilon_2);\ \varepsilon_2<2I\le\varepsilon_1<4I-\varepsilon_2\bigr]=E\bigl[Z(\varepsilon_2,\varepsilon_1);\ \varepsilon_2\ge 2I,\ \varepsilon_1<4I-\varepsilon_2\bigr],$$
--   2. $$E\bigl[Z(\varepsilon_1,\varepsilon_2);\ \varepsilon_2<2I,\ \varepsilon_1\ge 4I-\varepsilon_2\bigr]=E\bigl[Z(\varepsilon_2,\varepsilon_1);\ \varepsilon_2\ge 2I,\ 4I-\varepsilon_2\le\varepsilon_1<2I\bigr].$$
--
--   In the paper's notation these are the iterated-integral identities (a) and (b) of Lemma A.1. They are what makes the transfer payments cancel at symmetric profiles, so that the equilibrium profit does not depend on $t$ except through the service level.
--
--   **Formalization Note.** The expectations are Bochner integrals of region indicators times $Z$; the identities hold for every $Z$ (both sides are the same integral after the coordinate swap), so no integrability or measurability assumption on $Z$ is imposed. Region endpoints are chosen so that the swapped regions coincide exactly; the paper's closed limits differ from them by null sets.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), Online Appendix p. 2 (PDF 34), Lemma A.1(a)–(b)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem lemma_A1 (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1) (Z : ℝ → ℝ → ℝ) :
    (∫ ω, (if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then Z ω.1 ω.2 else 0) ∂ν
      = ∫ ω, (if 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2 then Z ω.2 ω.1 else 0) ∂ν) ∧
    (∫ ω, (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1 then Z ω.1 ω.2 else 0) ∂ν
      = ∫ ω, (if 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I then Z ω.2 ω.1 else 0) ∂ν) := by sorry

end InvShareComp.Exog
