-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroGrowthContourBounded_zero_from_growth_additional_loss_bounded
-- name    : OAI.SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:20.033568+00:00
-- url     : https://prove2.me/theorems/33c53641-192c-4683-8f7f-7972968d2ecf
-- title:
--   The zero-stage bound follows from the zero-growth bound
-- statement:
--   For reals $0<a\le1/4$, $b\ge1$, $b_\Phi>0$, $\varepsilon>0$, $M_{\mathrm{cap}},B_{\mathrm{mask}}\ge0$ and $L_{\mathrm{original}}$ there are $0<d\le1$ and $L>0$ with $L_{\mathrm{original}}\le L=\max(L_{\mathrm{original}},M_{\mathrm{cap}}+B_{\mathrm{mask}}+2d)+1\le\max(L_{\mathrm{original}},M_{\mathrm{cap}}+B_{\mathrm{mask}}+2)+1$ such that for every finite $S$ there are $J$, a finite $U$ and $C>0$ with: for all sufficiently large $Z$ ($Z>1$), every $\ell\ge0$, ideal $Q$, degree and $K\ge0$, `ZeroGrowthAt Q a b bΦ Bmask L Mcap ℓ Z degree S K` implies `ZeroAt Q a b bΦ Bmask Loriginal Mcap (ℓ+ε) Z J U (C(K+1))`.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded` in `lean/OAI/NumberTheory/DirichletL/Energy/ZeroGrowthContourBounded.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyZeroGrowth CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalRowSource QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem zero_from_growth_additional_loss_bounded (a b bΦ ε Mcap Bmask Loriginal:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L:ℝ,0<d ∧ d≤1 ∧ 0<L ∧ Loriginal≤L ∧
      L=max Loriginal (Mcap+Bmask+2*d)+1 ∧
      L≤ max Loriginal (Mcap+Bmask+2)+1 ∧
      ∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(ell:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤ell→0≤K→
        ZeroGrowthAt Q a b bΦ Bmask L Mcap ell Z degree S K→
        ZeroAt Q a b bΦ Bmask Loriginal Mcap (ell+ε) Z J U (C*(K+1)):= by
  sorry

end SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded

end

end OAI
end
