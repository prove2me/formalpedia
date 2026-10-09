-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_original_ray_compensatedPhysicalProbe_low_loss
-- name    : OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:14:29.044977+00:00
-- url     : https://prove2.me/theorems/165d6ecf-6cc9-45a7-a435-6f9f4d4ec840
-- title:
--   The compensated physical probe is O(Z^(3/16+loss))
-- statement:
--   Let $S$ be a finite set of maximal ideals with `SourceExclusions S`, $\ell:\mathrm{Fin}\,K\to\mathbb R$ injective, nonnegative with $\sum\ell_i\le1/6$, $R$ a set of ideals, $0<a\le b$, $B$, `loss` $>0$, slot weights $W_i$ supported in $[a,b]$ and bounded by $B$, and smooth $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$, $a_1<b_1$) bounded by $B_0,B_1\ge0$. Then for every `HeckeFamily.Character` $\eta$ there is $C>0$ such that for all sufficiently large $Z$,
--   $$\|\texttt{compensatedPhysicalProbe}\,\eta\,(\texttt{calibrationForSet}\,S)\,W_0\,W_1\,(i\mapsto\texttt{canonicalSlotSupport}(\texttt{pool}\,R\,S\,a\,b\,Z^{\ell_i}))\,W\,(Z^{\ell_i})\,Z^{17/48}\,Z^{23/48}\,Z\|\le C\,Z^{3/16+\mathrm{loss}}.$$
--
--   Lean: `OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low_loss` in `lean/OAI/NumberTheory/DirichletL/Detector/LowWindowBound.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem original_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤1/6) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤C*Z^(3/16+loss) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
