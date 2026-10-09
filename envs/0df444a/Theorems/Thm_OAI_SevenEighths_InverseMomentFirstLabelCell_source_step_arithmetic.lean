-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMomentFirstLabelCell_source_step_arithmetic
-- name    : OAI.SevenEighths.InverseMomentFirstLabelCell.source_step_arithmetic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:51.179331+00:00
-- url     : https://prove2.me/theorems/3d7f4e2e-78bc-4ad9-bc76-f6b646d60663
-- title:
--   A first-label source satisfies the second-source conditions
-- statement:
--   Let $p$ be a family of nonzero Eisenstein integers generating maximal ideals, `pool`, $Q$ with cube primary products $\le Z^{\ell+\eta}$, a source index $k$, $l,j$, `negative`, slot lists, and reals $Z>1$, $\eta\ge0$ with $Z^\eta\ge2$, $\varepsilon\ge0$, $e^{\mathrm{window}}\le Z^{4\eta}$, and $L_{\mathrm{col}},L_Y,L_{\mathrm{cap}},\pi$ with `columnScale`$\cdot e^{\mathrm{window}}\le Z^{L_{\mathrm{col}}}$, `firstCellRadius`$^{-1}\le Z^{L_Y}$, $b\cdot$`columnScale` $\le Z^{L_{\mathrm{cap}}}$, `exponent Z (k 3)` $+\eta+2L_{\mathrm{col}}+\tau+L_Y\le L_{\mathrm{cap}}$, and the mass budget $\varepsilon(\ell+\texttt{exponent}(k\,4)/2+\texttt{exponent}\,l+L_{\mathrm{cap}}+11\eta/2)\le\pi$. Then the source $S=$`source p pool Q k l j negative J lists Z M r ℓ V η τ window b` satisfies `ActualSecondSourceConditions`; all its second frequencies are nonzero and lie in the `nonzeroChildFrequencyBall` of radius `actualCellRowRadius …`; every key has nonnegative row exponent; each point has cube primary products $\le Z^{\ell+\eta}$, active support $\le Z^{\texttt{exponent}(k\,4)+\eta}$, first common part $\le Z^{\texttt{exponent}(k\,2)+\eta}$, quotient norm $\le Z^{\texttt{exponent}\,l+\eta}$, `jLabel` size between $Z^{\texttt{exponent}\,j\mp\eta}$ and first divisor $\le Z^{\texttt{exponent}(k\,3)+\eta}$; every child label lies in `actualCellLabels`, whose squarefree members are nonzero with norm $\le Z^{\texttt{actualCellLabelExponent}}$; outer norms are $\le Z^{L_{\mathrm{cap}}}$; source common·overlap $\le b\cdot$`columnScale`; and every key satisfies the mass budget $\varepsilon(\texttt{secondCount}(\dots)+11\eta/2)\le\pi$.
--
--   Lean: `OAI.SevenEighths.InverseMomentFirstLabelCell.source_step_arithmetic` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstLabelCellStepData.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_step_arithmetic (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (heps : 0≤eps)
    (hwindow : Real.exp window≤Z^(4*eta))
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ActualSecondSourceConditions p S ∧
    (∀x∈S,x.second.frequency≠0) ∧
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) ∧
    (∀x∈S,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(exponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(exponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(exponent Z l+eta) ∧
      Z^(exponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(exponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(exponent Z (k 3)+eta)) ∧
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) ∧
    (∀x∈S,∀i,outerNorms p x i≤Z^Lcap) ∧
    (∀x∈S,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative) ∧
    (∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi) := by
  sorry

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end
