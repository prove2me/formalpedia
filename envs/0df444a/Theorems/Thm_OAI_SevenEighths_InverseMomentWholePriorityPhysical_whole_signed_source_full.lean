-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMomentWholePriorityPhysical_whole_signed_source_full
-- name    : OAI.SevenEighths.InverseMomentWholePriorityPhysical.whole_signed_source_full
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:52:27.20907+00:00
-- url     : https://prove2.me/theorems/02544410-2ea4-4f70-bbbe-d5ead5abd13d
-- title:
--   Whole signed source sum regrouped by assigned parents
-- statement:
--   Let $p$ be a family of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda`, with residue characteristic $\ne2$ and `goodLambda`$^2\mid p_i-1$; `extra`, `pool`, a finite set of sources `Source ι Jo` with weights $w$, `negative`, $\Psi$, $m$, slots and a subset $J$ with lists and coefficients $a$, a Schwartz $\omega$ supported in $[lo,hi]$ ($lo>0$), reals $X,Y>0$, $t$, a pair of ray characters $r$, a core index, a cutoff $R$ and a label map. Then
--   $$\sum_{x}w(x)\,\big\|\texttt{primeMark}\,J\,\mathrm{lists}\,a\,(\texttt{wholeExtractedSupport}\dots x)\big\|^2\texttt{parentPoisson}(\dots,\mathrm{lists}\setminus\texttt{extra},\dots,\omega,X,t,Y,r,\mathrm{core},\texttt{parent}\,p\,x)=\sum_{y\in\texttt{wholeAssignedParents}}\texttt{coefficient}\,p\,J\,a\,w\,y\cdot\texttt{fullPhysical}(\dots,\texttt{principalWindow}\,\omega\dots t,X,Y,r,\mathrm{core},R,\mathrm{label},y).$$
--
--   Lean: `OAI.SevenEighths.InverseMomentWholePriorityPhysical.whole_signed_source_full` in `lean/OAI/NumberTheory/DirichletL/Descent/WholePriorityPhysical.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityPhysical
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InverseMomentWholePriorityParents InversePrioritySecondSource
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
variable {Jo : ℕ} (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem whole_signed_source_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (Source ι Jo)) (w : Source ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ x∈source,w x*(‖primeMark J lists a
      (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J
        (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x)) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  sorry

end SevenEighths.InverseMomentWholePriorityPhysical

end

end OAI
end
