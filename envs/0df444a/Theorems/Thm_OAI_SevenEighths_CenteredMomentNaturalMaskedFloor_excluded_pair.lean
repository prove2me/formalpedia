-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentNaturalMaskedFloor_excluded_pair
-- name    : OAI.SevenEighths.CenteredMomentNaturalMaskedFloor.excluded_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:49.777143+00:00
-- url     : https://prove2.me/theorems/3f986d54-e8d4-4c6e-b683-daabd218fc0b
-- title:
--   Radial energy of a pair of excluded smoothed sums
-- statement:
--   For reals $a>0$, $b\ge0$, $\varepsilon>0$ there are a finite $S\subseteq\mathbb N\times\mathbb N$ and $C>0$ such that for all Schwartz $W_1,W_2$ supported in $[a,b]$, every family of characters $\chi_z$ ($z\in\mathcal O$, `HeckeFamily.O`), every `Radial` datum $r$, every nonzero ideal $R$ and reals $Q\ge0$, $X_1,X_2>0$, if every kept $z$ (`r.keep`) has nontrivial residue character and modulus norm $\le Q$, then
--   $$\texttt{radialEnergy}\big(z\mapsto\texttt{polynomial}(\texttt{excluded}\,\chi_z\,R)\,\mathrm{false}\,W_1\,X_1\,0\,0\cdot\texttt{polynomial}(\texttt{excluded}\,\chi_z\,R)\,\mathrm{false}\,W_2\,X_2\,0\,0\big)\le C\,N(\operatorname{rad}R)^{\varepsilon}\,\texttt{diagonalControl}(r.\mathrm{profile})\max(1,r.\mathrm{scale})\big(\|W_1\|_S\|W_2\|_S\big)^2Q^4,$$
--   the energy taken with `r.keep`, `r.profile`, `r.scale`, and $\|\cdot\|_S$ the supremum of the Schwartz seminorms indexed by $S$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentNaturalMaskedFloor.excluded_pair` in `lean/OAI/NumberTheory/DirichletL/Moments/NaturalMaskedFloor.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalMaskedFloor
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentCoreFloor CenteredMomentLattice CenteredMomentTwist
open HeckeInverseAmplification
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

theorem excluded_pair (a b ε : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (χ : O→Character) (r : Radial) (R : Ideal O) (Q X₁ X₂ : ℝ), R≠0 →
      0≤Q → 0<X₁ → 0<X₂ →
      (∀z,r.keep z→(χ z).residue≠1) →
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤Q) →
    radialEnergy (fun z=>polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4 := by
  sorry

end SevenEighths.CenteredMomentNaturalMaskedFloor

end

end OAI
end
