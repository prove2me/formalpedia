-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_priority_source_moving_radius_window_order_uniform_types
-- name    : OAI.SevenEighths.InverseMoment.actual_priority_source_moving_radius_window_order_uniform_types
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:30.05659+00:00
-- url     : https://prove2.me/theorems/4356cf03-e7b7-481e-b1c5-8da2662d4899
-- title:
--   Priority-source second rows bounded cell by cell through column energies
-- statement:
--   Let $\omega,\Phi$ be Schwartz functions with $\omega$ supported in $[lo,hi]$, $lo>0$, `negative` a Boolean, $B_0:\mathrm{Fin}\,6\to\mathbb R$ nonnegative, $K\in\mathbb N$ and $\varepsilon_{\mathrm{mass}}>0$. Then there are Schwartz functions $\omega_1,\omega_2$, compactly supported with topological support in $[lo_F,hi_F]$ where $0<lo_F\le hi_F$, such that for every $J\in\mathbb N$ there is $C\ge0$ with the following property. For every family $p:\iota\to\mathcal O$ of nonzero Eisenstein integers (`ActualEisensteinCubic.O`) generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda`, with `goodLambda`$^2\mid p_i-1$ and residue characteristic $\ne2$; every finite set `source` of `MarkedSecondSource ι Jo 0` satisfying `ActualSecondSourceConditions`; a finite `pool`, multiplicative $\Psi$ bounded by 1, $m$, a `SecondRayIndex` $z$, two slot systems (`slots₁`, `lists₁`, $a_1$ and `slots₂`, `lists₂`, $a_2$, coefficients bounded by 1, at most $K$ slots each, $J_o\le2K$), deleted sets lying in the cube support, first common part or dividing the quotient, and reals and functions $Y>0$, $R$, $L\ge0$, $Z>1$, $X>0$, $\varepsilon_{\mathrm{child}}$, `Vlabel`, $\ell$, $R_{\mathrm{active}}$, $j$, `tcount`, $\eta\ge0$ with $Z^\eta\ge2$, $\rho$ with $|\rho_i|\le B_0(i)$, $t$, weights $w$ bounded by 1, `labels` and $A\ge0$ — under the size hypotheses on each source point (second frequency in `nonzeroChildFrequencyBall`, cube primary products of size $\le Z^{\ell+\eta}$, active support $\le Z^{R_{\mathrm{active}}+\eta}$, `jLabel` size $\ge Z^{j-\eta}$, quotient norm $\le Z^{\mathrm{tcount}+\eta}$), child labels in `labels d` for each cell key $d$, and the two families of `normalizedColumnEnergy` bounds (for `secondRayMinus` with $\omega_1$ and `secondRayPlus` with $\omega_2$, by $A\,Z^{\max(0,c_d)+\mathrm{Vlabel}(d)+\varepsilon_{\mathrm{child}}}$ times `tripleHeight J`·`coordinateHeight J`, $c_d=$`secondCellColumnExponent Z X d`): the norm of $Y\cdot$`secondRayCoefficient z` times the sum over the source of $w(x)$·`actualSecondSignedWeight`·`actualSecondProfileRow` (with the `principalWindow` tests and the deleted lists) is at most
--   $$\sum_{d\in\texttt{keys}}e^{6L}\Big\|\frac{Y\,\texttt{secondRayCoefficient}\,z}{s_1(d)s_2(d)Z^{c_d}}\Big\|\cdot36\cdot2^{|\mathrm{slots}_1|+|\mathrm{slots}_2|}A\,Z^{2(\max(0,c_d)+\mathrm{Vlabel}(d))+\varepsilon_{\mathrm{child}}}Z^{(\ell+R_{\mathrm{active}}/2-j+\mathrm{tcount}+e_0(d)-e_1(d)+11\eta/2)(1+\varepsilon_{\mathrm{mass}})}\cdot C(1+|h|)^{k}(1+|h|)^{k},$$
--   with $s_i=$`scales d i`, $e_i=$`secondCellExponent Z d i`, $h=$`priorityHeight negative t` and $k=$`InverseClippingProfiles.momentOrder J` (the Lean statement also carries a trivial factor $(1+\dots)^0$).
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_priority_source_moving_radius_window_order_uniform_types` in `lean/OAI/NumberTheory/DirichletL/Descent/PriorityMovingRadiusWindowOrderUniform.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_source_moving_radius_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
