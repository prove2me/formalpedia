-- Prove2me | Theorems.Thm_InvShareComp_Exog_proposition_1a
-- name    : InvShareComp.Exog.proposition_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:00.546088+00:00
-- url     : https://prove2.me/theorems/3951105d-f75e-480b-9e49-5b4df291094f
-- title:
--   Proposition 1(a), p. 15 (PDF 15), via the identity of its proof (OA p. 9) — ŝ(t, I) − ŝᴺ(I) = (c̄ − 2t − δ)βW/(2k)
-- statement:
--   Under the standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density, $I\in[0,1]$ and $t\in[0,\bar c-\delta]$, let
--   $$W(I)=E\bigl[\varepsilon_1;\ \varepsilon_2<2I\le\varepsilon_1<4I-\varepsilon_2\bigr]+E\bigl[\varepsilon_2;\ \varepsilon_2<2I,\ \varepsilon_1\ge4I-\varepsilon_2\bigr]\ \ge 0 .$$
--   Then
--   $$\hat s(t,I)-\hat s^N(I)=\frac{(\bar c-2t-\delta)\,\beta\,W(I)}{2k}.$$
--   Consequently $\hat s(t,I)\ge\hat s^N(I)$ when $t<\frac{\bar c-\delta}2$ and $\hat s(t,I)\le\hat s^N(I)$ when $t>\frac{\bar c-\delta}2$; if moreover $\beta>0$ and $W(I)>0$, both inequalities are strict.
--
--   Sharing intensifies service competition at low transfer prices and softens it at high ones, with the switch exactly at $(\bar c-\delta)/2$.
--
--   **Formalization Note.** The paper states the strict inequalities; they need $\beta>0$ and positive probability of a shared transaction ($W(I)>0$), which fail e.g. at $I=0$. Both the weak conclusion and the strict one under these explicit conditions are stated.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), p. 15 (PDF 15), Proposition 1(a); identity from the proof, Online Appendix p. 9 (PDF 41)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem proposition_1a (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) :
    sHat P ν t I - sHatN P ν I = (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) ∧
    0 ≤ Wval ν I ∧
    (t < (P.cbar - P.δ) / 2 → sHatN P ν I ≤ sHat P ν t I) ∧
    ((P.cbar - P.δ) / 2 < t → sHat P ν t I ≤ sHatN P ν I) ∧
    (0 < P.β → 0 < Wval ν I →
      (t < (P.cbar - P.δ) / 2 → sHatN P ν I < sHat P ν t I) ∧
      ((P.cbar - P.δ) / 2 < t → sHat P ν t I < sHatN P ν I)) := by sorry

end InvShareComp.Exog
