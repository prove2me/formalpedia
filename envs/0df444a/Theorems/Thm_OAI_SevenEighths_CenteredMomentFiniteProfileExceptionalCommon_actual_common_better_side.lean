-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptionalCommon_actual_common_better_side
-- name    : OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_common_better_side
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:23:40.321747+00:00
-- url     : https://prove2.me/theorems/2e3c8107-9831-4e58-be02-8f012442b039
-- title:
--   Paired normalized columns: the better side
-- statement:
--   For $w_{lo}>0$, $w_{hi}\ge0$, $\iota$ finite, $lo,hi$, $\varepsilon,\delta,\theta>0$, $B,L_{\mathrm{bound}}\ge0$ there are $J$ and $S_{\mathrm{profile}}\ni(0,0)$ such that for every nonzero $Q$ there is $K>0$ with: eventually in $Z$, for inputs $s,v$ with bounds $lo,hi$, slot sizes $\ge1$ and test pairs from `Profiles` $p,q$, `Supported` $C,D$ with a common divisor `seed`, $R\ne0$, and the scale, row and conductor hypotheses of the Lean, and ideals $D_s$ of norm $\le Z^{L_{\mathrm{bound}}}$ where $\mu\ne0$:
--   $$\sum_{L\in D_s}|\mu(L)|\sum_z\|\texttt{normalizedColumn}\,s\,C\dots\|\,\|\texttt{normalizedColumn}\,v\,D\dots\|\le K|\mathrm{rows}|Z^{2\varepsilon+\delta-\max(\max(r_L-\log_ZN(C),0),\max(r_R-\log_ZN(D),0))}(N(C)N(D))^{\theta}\frac{\texttt{profileMass}\cdot\texttt{frozenProfile}\,s\cdot\texttt{frozenProfile}\,v}{N(C)N(D)}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_common_better_side` in `lean/OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalCommonSymmetry.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalMaskedSource
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalSourceShell
open CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_common_better_side (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s v:Input ι)(p q:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,v.lo i=lo i) → (∀i,v.hi i=hi i) →
      (∀i,1≤ s.P i) → (∀i,1≤v.P i) →
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → v.W₁=q.profile 0 → v.W₂=q.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀rLeft rRight:ℝ,
      Z^rLeft≤ s.X₁ → Z^rLeft≤ s.X₂ → Z^rLeft≤ s.Y₁ → Z^rLeft≤ s.Y₂ →
      Z^rRight≤v.X₁ → Z^rRight≤v.X₂ → Z^rRight≤v.Y₁ → Z^rRight≤v.Y₂ →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow s.η Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow v.η Q fixedBadMask 1 z) →
      (∀z∈rows,(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,(v.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
        K*(rows.card:ℝ)*Z^(2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
            (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (profileMass Sprofile s.toData v.toData p q J*frozenProfile s*frozenProfile v/
            ((C.absNorm:ℝ)*D.absNorm)) := by
  sorry

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end
