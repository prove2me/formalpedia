-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroUnbalancedOriginal_original_unbalanced_from_zero_low
-- name    : OAI.SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal.original_unbalanced_from_zero_low
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:30:24.146458+00:00
-- url     : https://prove2.me/theorems/260e7487-e5da-4417-a79f-59d3fe4a3785
-- title:
--   Unbalanced zero-stage energies from the low bound
-- statement:
--   For reals $0<a\le1/4$, $b\ge1$, $b_\Phi>0$, $\rho>0$, $\varepsilon>0$, $M_{\mathrm{cap}},B_{\mathrm{mask}}\ge0$ there are $d>0$, $0<\xi\le\rho/100$ and $L$ with $M_{\mathrm{cap}}+B_{\mathrm{mask}}+\xi\le L\le M_{\mathrm{cap}}+B_{\mathrm{mask}}+\rho/100$ such that for every finite $S$ there are $J$, $U$, $C>0$ with: for all sufficiently large $Z$, whenever `ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K` holds ($e,K\ge0$), for every `NaturalState` $s$ with fixed modulus $Q$ and $\rho\le\mathrm{width}\le M_{\mathrm{cap}}$, every `Profiles a b` $p$, $t$ and $X_1,X_2>0$ with $\min(\ell_1,\ell_2)\le\mathrm{width}/4$ and $\tfrac56\mathrm{width}\le\ell_1+\ell_2$: `s.plainEnergy p t X₁ X₂` $\le C(K+1)\,\texttt{diagonalControl}\,(p.\texttt{control}\,U)^2(1+|t|)^JZ^{\mathrm{width}+e+\varepsilon}$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal.original_unbalanced_from_zero_low` in `lean/OAI/NumberTheory/DirichletL/Energy/ZeroUnbalancedOriginal.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

theorem original_unbalanced_from_zero_low
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤e → 0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q → rho≤ s.width →s.width≤Mcap →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂ →
      s.plainEnergy p t X₁ X₂ ≤
        C*(K+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^J*Z^(s.width+e+ε):= by
  sorry

end SevenEighths.CenteredMomentEnergyZeroUnbalancedOriginal

end

end OAI
end
