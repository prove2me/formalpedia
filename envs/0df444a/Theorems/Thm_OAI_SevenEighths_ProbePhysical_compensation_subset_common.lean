-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_compensation_subset_common
-- name    : OAI.SevenEighths.ProbePhysical.compensation_subset_common
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:51.397739+00:00
-- url     : https://prove2.me/theorems/022fb521-3322-4a9e-8f7d-e2f3a645ef14
-- title:
--   Compensation subset probes as a dyadic sum of Gaussian integrals
-- statement:
--   Let $J\subseteq\mathrm{Fin}\,K$, $W:\mathrm{Fin}\,K\to\mathbb R\to\mathbb C$, $V$ a compactly supported Schwartz function such that for all $R,x>0$ and positive $q$ on the selected slots, `gaussianAnnulus x`$\cdot\prod_iW_i(q_i)\cdot$`gaussianMellinProfile (R x/∏q)` equals $\int V^*(\texttt{normTwistedSource gaussianFixedWindow}\,t)(x)\prod_iW_i(q_i)\texttt{logPhase}(-t)(\log q_i)\,\texttt{gaussianJointDensity}\,V\,R\,t\,dt$ (hypothesis `hsep`). Then for every `HeckeFamily.Character` $\eta$, `CalibrationData` $C$, compactly supported $W_0,W_1$, finite $F$, families $p_k$ of nonzero elements, $P_i>0$ and $X,Y,Z>0$:
--   $$\sum_{k\in F}\prod_iW_i(\texttt{elementNorm}(p_{k,i})/P_i)\,\texttt{compensationSubsetProbe}(\dots,p_k,J,X,Y,Z)=\sum_{j\ge0}\int\Big(\sum_k\texttt{compensationSubsetWeight}\cdots\texttt{compensationRowTest}(\dots,2^j,t)\,\texttt{selectedSlotFactor}(\dots,t)\Big)\texttt{gaussianJointDensity}\,V\Big(\frac{2^j}{Z\prod_{i\notin J}P_i}\Big)(t)\,dt.$$
--
--   Lean: `OAI.SevenEighths.ProbePhysical.compensation_subset_common` in `lean/OAI/NumberTheory/DirichletL/Detector/GaussianSubset.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensation_subset_common {K : ℕ} {α : Type*}
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : SelectedSlot J→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i.val (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i.val (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (p : α→Fin K→O) (hp : ∀k∈F,∀i,p k i≠0)
    (P : Fin K→ℝ) (hP : ∀i,0<P i) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑k∈F,(∏i,W i (elementNorm (p k i)/P i))*compensationSubsetProbe η C W0 W1 (p k) J X Y Z)=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,compensationSubsetWeight η W P (p k) J*
        compensationRowTest η C W0 W1 (p k) J X Y ((2:ℝ)^j) t*
          selectedSlotFactor W P (p k) J t)*
            gaussianJointDensity V hV ((2:ℝ)^j/(Z*∏i∈Finset.univ\J,P i)) t := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
