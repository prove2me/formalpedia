-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFiniteProfileExceptionalCommon_actual_paired_capped
-- name    : OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_paired_capped
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:14:21.215247+00:00
-- url     : https://prove2.me/theorems/31b73fdc-6eed-41be-95c4-8a7204e4ba12
-- title:
--   Paired amplitude bound for exceptional profiles
-- statement:
--   For $w_{lo}>0$, $w_{hi}\ge0$, $\varepsilon>0$, $B\ge0$ there are $J$ and a finite $S_{\mathrm{profile}}\ni(0,0)$ such that for every nonzero ideal $Q$ there is $C>0$ with: for all finite types $\alpha,\kappa$, `Data` $s,v$, `Profiles` $p,q$ (between $w_{lo},w_{hi}$), reals $Z>1$, $r,r_{\mathrm{right}}$, every $z$ that is `ProfileAdmissible` for $(s,p,Q,Z,B,r)$ and $(v,q,Q,Z,B,r_{\mathrm{right}})$, every ideal $D$ and allocations $a,b$ of $D$:
--   $$\|\texttt{amplitude}\,s\,D\,a\,z\|\,\|\texttt{amplitude}\,v\,D\,b\,z\|\le C\,p.\mathrm{control}\,q.\mathrm{control}\,Z^{2\varepsilon}(1+|s.t|)^J(1+|v.t|)^J\,\texttt{slotControl}\,s\,\texttt{slotControl}\,v\sqrt{\texttt{volume}\,s}\sqrt{\texttt{volume}\,v}\,\texttt{exceptionalWeight}(\dots,D,a,b,Z,\max(r,0)).$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentFiniteProfileExceptionalCommon.actual_paired_capped` in `lean/OAI/NumberTheory/DirichletL/Moments/FiniteProfileExceptionalCommonAsymmetric.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

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

theorem actual_paired_capped (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(ε B:ℝ) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧
      ∀(α κ:Type u) [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ],
      ∀(s:Data α)(v:Data κ)(p q:Profiles wlo whi)(Z r rRight:ℝ),1<Z → ∀z:O,
      ProfileAdmissible s p Q Z B r z → ProfileAdmissible v q Q Z B rRight z →
      ∀(D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
        (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2))),
      ‖amplitude s D a z‖*‖amplitude v D b z‖≤
        C*p.control Sprofile*q.control Sprofile*Z^(2*ε)*(1+‖s.t‖)^J*(1+‖v.t‖)^J*
          slotControl s*slotControl v*Real.sqrt (volume s)*Real.sqrt (volume v)*
            exceptionalWeight s.toSource v.toSource D a b Z (max r 0):= by
  sorry

end SevenEighths.CenteredMomentFiniteProfileExceptionalCommon

end

end OAI
end
