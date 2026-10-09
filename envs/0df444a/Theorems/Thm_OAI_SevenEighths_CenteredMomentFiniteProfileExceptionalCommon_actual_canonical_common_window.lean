-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptionalCommon_actual_canonical_common_window
-- name    : OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_canonical_common_window
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:36.99651+00:00
-- url     : https://prove2.me/theorems/b40f2931-3973-47dd-8d5b-86c979648079
-- title:
--   Canonical common window columns bound
-- statement:
--   Let $w_{lo}>0$, $w_{hi}\ge0$, $\iota$ finite, $lo,hi:\iota\to\mathbb R$, reals $\varepsilon,\delta,\theta>0$, $B,L_{\mathrm{bound}}\ge0$. Then there are $J$ and a finite $S_{\mathrm{profile}}\ni(0,0)$ such that for every ideal $Q\ne0,\ne\top$ with $Q\le(72)$ there is $K>0$ with: for all sufficiently large $Z$ ($Z>1$), all `Input`s $s,v$ with bounds $lo,hi$, slot sizes $P_i\ge1$ and test pairs given by `Profiles` $p,q$, `Supported` ideals $C,D$ with a common divisor `seed`, $R\ne0$, reals $r_{\mathrm{Left}},r_{\mathrm{Right}}$ with all four scales of $s$ at least $Z^{r_{\mathrm{Left}}}$ and of $v$ at least $Z^{r_{\mathrm{Right}}}$, nonzero `rows` that are `FixedInducingRow` for $s.\eta$, $v.\eta$ and for `childCharacter η₀ χ` (with the common/nonunit frequency generator of $C,D,U$), the conductor-size conditions by $Z^B$, $Q$ coprime to $C$, `idealCoeff η₀ C` $\ne0$, $m\ne0$ with `goodLambda`$\mid m$, $2\mid m$, $C_r\ge0$, $M$ with row norms $\le C_rZ^M$, $\theta_1,\theta_2$, $X,Y>0$, and squarefree-weighted ideals $D_s$ of norm $\le Z^{L_{\mathrm{bound}}}$:
--   $$\sum_{L\in D_s}|\mu(L)|\sum_{z}\|\texttt{windowColumn}\,s\,C\dots X\dots z\|\,\|\texttt{windowColumn}\,v\,D\dots Y\dots z\|\le K\cdot768\cdot6^{\omega(Q)}C_r^{1/6}\,Z^{e}\,(N(C)N(D))^{\theta}\frac{\texttt{frozenProfile}\,s\cdot\texttt{frozenProfile}\,v}{N(C)N(D)}\,\texttt{mass}(\dots)\Big(\int(1+|u|)^J|\texttt{columnDensity}(u)|\,du\Big)^2,$$
--   where $\omega(Q)$ is the number of distinct prime factors of $Q$ and the exponent $e$ is the expression in $M$, the `forcingIdeal`, $\varepsilon,\delta$ and $\max(\max(r_{\mathrm{Left}}-\log_ZN(C),0),\max(r_{\mathrm{Right}}-\log_ZN(D),0))$ given in the Lean.
--
--   Lean: `OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_canonical_common_window` in `lean/OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalCommonWindow.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalCost
open CenteredMomentCommonPairedSource CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonWindowColumn
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth
open CenteredMomentSecondHeightFamily CenteredMomentLogDyadic
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_common_window (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
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
      ∀(η₀:Character)(χ:RayFourExpansion.RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀θ₁ θ₂ X Y:ℝ,0<X → 0<Y →
      ∀Ds:Finset (Ideal O),(∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) →
      (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L s.η s.t θ₁ X logAnnulus z‖*
        ‖windowColumn v D hD R seed L v.η v.t θ₂ Y logAnnulus z‖)≤
        K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (max (rLeft-Real.logb Z (C.absNorm:ℝ)) 0)
              (max (rRight-Real.logb Z (D.absNorm:ℝ)) 0))*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          (frozenProfile s*frozenProfile v/((C.absNorm:ℝ)*D.absNorm))*
          mass Sprofile s v p q s.t v.t θ₁ θ₂ J*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2 := by
  sorry

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end
