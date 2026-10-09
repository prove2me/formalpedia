-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptionalCommon_actual_whole_asymmetric
-- name    : OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_whole_asymmetric
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:15:07.284873+00:00
-- url     : https://prove2.me/theorems/a2378609-8b01-48f6-a2e8-fbd2868ed201
-- title:
--   Asymmetric exceptional source sum bound for profiles
-- statement:
--   Let $w_{lo}>0$, $w_{hi}\ge0$, $\iota$ finite, $lo,hi:\iota\to\mathbb R$, $\varepsilon,\delta>0$, $B,L_{\mathrm{bound}}\ge0$. Then there are $J$ and a finite $S_{\mathrm{profile}}\ni(0,0)$ such that for every nonzero ideal $Q$ there is $C>0$ such that for all sufficiently large $Z$ ($Z>1$), finite $I,L\subseteq\iota$, `Data` $s$ on $I$, $v$ on $L$ (bounds of $v$ equal to $lo,hi$), `Profiles` $p,q$, reals $r,r_{\mathrm{right}}$, rows that are `ProfileAdmissible` for both, and ideals $D_s$ of norm $\le Z^{L_{\mathrm{bound}}}$ where $\mu\ne0$:
--   $$\sum_{D}|\mu(D)|\sum_a\sum_b\sum_{z\in\mathrm{rows}}\|\texttt{amplitude}\,s\,D\,a\,z\|\,\|\texttt{amplitude}\,v\,D\,b\,z\|\le C|\mathrm{rows}|Z^{2\varepsilon+\delta-\max(r,0)}\,\texttt{profileMass}\,S_{\mathrm{profile}}\,s\,v\,p\,q\,J.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_whole_asymmetric` in `lean/OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalCommonAsymmetric.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalCommon
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalAllocationShell
open CenteredMomentExceptionalMaskedSource UniqueFactorizationMonoid CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

theorem actual_whole_asymmetric (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Profiles wlo whi),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r rRight:ℝ,∀rows:Finset O,(∀z∈rows,ProfileAdmissible s p Q Z B r z) →
      (∀z∈rows,ProfileAdmissible v q Q Z B rRight z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
          ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-max r 0)*profileMass Sprofile s v p q J:= by
  sorry

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end
