-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_3
-- name    : GEPPGrowth.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:56.628683+00:00
-- url     : https://prove2.me/theorems/be963e1f-5251-469a-bfce-2acbb40afa6b
-- title:
--   Lemma 4.3 — Maximum of independent Gaussian absolute values
-- statement:
--   Let $x_1,\ldots,x_n$ be independent standard normal variables. Let $M:=\max_i|x_i|$. Then,
--   for every $t>0$,
--
--   $$
--   \Pr(M\ge t)\le\dfrac{n\sqrt2}{t\sqrt\pi}\exp\left(-\dfrac{t^2}{2}\right)
--   $$.
--
--   This controls the maximum of any positive finite family, including the input matrix entries.
--
--   Differences from the source:
--   - encoding: n independent standard normal variables with n positive → the canonical n-coordinate Gaussian product law and its finite absolute maximum; reason: the joint distribution is identical and n>0 keeps the source maximum defined
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.3, printed p.8, PDF p.9

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.3, printed p.8 / PDF p.9. The product law is precisely independence of the n standard normal variables. -/
theorem lemma_4_3 (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    prob (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      {x | t ≤ maxEntry (fun i (_ : Fin 1) => x i)} ≤
        (n:ℝ)*Real.sqrt 2 / (t*Real.sqrt Real.pi) * Real.exp (-t^2/2) := by sorry

end GEPPGrowth.Main
