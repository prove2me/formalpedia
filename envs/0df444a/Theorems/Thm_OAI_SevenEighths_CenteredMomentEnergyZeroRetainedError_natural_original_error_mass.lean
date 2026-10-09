-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroRetainedError_natural_original_error_mass
-- name    : OAI.SevenEighths.CenteredMomentEnergyZeroRetainedError.natural_original_error_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:21:43.843061+00:00
-- url     : https://prove2.me/theorems/1e6b21f7-699d-4dac-b356-90d3a3d1ae6b
-- title:
--   Error mass of natural long-short products
-- statement:
--   For $a>0$, $b\ge0$, $b_\Phi,\epsilon,\xi>0$ and `saving` there are $n$, a finite $S$ and $C>0$ such that, eventually in $Z$ ($Z>1$), for every natural state with mask $B_{\mathrm{mask}}$, Schwartz $W_{\mathrm{long}},W_{\mathrm{short}}$ supported in $[a,b]$, reals $t,\omega$, $X_{\mathrm{short}}>0$ and `along` $>$ width $+\xi$: the `radialEnergy` of $z\mapsto$`polynomial (naturalCharacter … z) false Wlong (Z^along) 0 t`·`polynomial … Wshort Xshort 0 ω` is at most
--   $$C\max(1,c_{\mathrm{fix}}b_\Phi Z^{\mathrm{width}})^{2\epsilon}\|W_{\mathrm{long}}\|_S^2\|W_{\mathrm{short}}\|_{0,0}^2(1+|t|)^{2n}Z^{-2\,\mathrm{saving}}\,\texttt{diagonalControl}\,\max(1,\mathrm{scale})\,X_{\mathrm{short}}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyZeroRetainedError.natural_original_error_mass` in `lean/OAI/NumberTheory/DirichletL/Energy/ZeroRetainedError.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroRetainedError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalPrimitive CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyZeroReflectionSupport CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyState
open CenteredMomentEnergyReferenceState CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem natural_original_error_mass (a b bΦ epsilon xi saving:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(state:NaturalState Z Bmask bΦ)(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(t omega along Xshort:ℝ),0<Xshort → state.width+xi<along →
      radialEnergy (fun z=>polynomial (naturalCharacter state.character z) false Wlong
          (Z^along) 0 t*polynomial (naturalCharacter state.character z) false Wshort Xshort 0 omega)
        state.radial.keep state.radial.profile state.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^state.width))^(2*epsilon)*
        (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
        QuadraticInitialBound.diagonalControl state.radial.profile*max 1 state.radial.scale*Xshort:= by
  sorry

end SevenEighths.CenteredMomentEnergyZeroRetainedError

end

end OAI
end
