-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_second_varying_balanced_profile_children
-- name    : OAI.SevenEighths.InverseMoment.actual_second_varying_balanced_profile_children
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:52:01.402081+00:00
-- url     : https://prove2.me/theorems/c3614102-55d3-4711-87b4-ca1275722c77
-- title:
--   Second profile rows as an integral of mode branches over unit sectors
-- statement:
--   Let $p$ be a family of nonzero Eisenstein integers generating maximal, pairwise coprime ideals avoiding `goodLambda`, with `goodLambda`$^2\mid p_i-1$, and `source` a finite set of `MarkedSecondSource ι Jo 0` with `ActualSecondSourceConditions`. Then there is a map `sector` from source points to pairs of units such that for every `pool`, $\Psi$, $m$, ray index $z$, two slot systems (with lists depending on the point), $W_1,W_2,\omega_1,\omega_2$, Schwartz $\Phi$, reals $G,E,V,B,X>0$, $Y,R,L$, $U:\mathrm{Fin}\,6\to\mathbb R\to\mathbb C$, an integrable density on `Frequency × (Fin 6 → ℝ)` and weights $w$: if the density represents $e^{-6L}$`secondPoissonProfile` $(\bar W_1,W_2,\Phi,U)$ at scale $YB/(EV^2X^2)$ as an integral of `pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope`, the second frequencies lie in `nonzeroChildFrequencyBall (actualSecondMultiplier p x) R`, $\omega_k$ equals 1 where $W_k$ is nonzero (at the relevant prime products), and $U_i=1$ at the `secondRelativeLog` coordinates of `secondProfileIndices`, then $e^{-6L}\cdot Y\,$`secondRayCoefficient z`$\sum_xw(x)\,$`actualSecondSignedWeight`·`actualSecondProfileRow` (scale $GVX$) equals
--   $$\frac{Y\,\texttt{secondRayCoefficient}\,z}{EVX}\int\mathrm{density}(t)\sum_{uv}\sum_{x\in\texttt{secondSourceSector}}w(x)\,\texttt{actualSecondSignedWeight}(\dots)\sum_{J_1\subseteq\mathrm{slots}_1}\sum_{J_2\subseteq\mathrm{slots}_2}\texttt{secondModeBranch}(\dots,uv,J_1,J_2,\dots,t)\,dt.$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_second_varying_balanced_profile_children` in `lean/OAI/NumberTheory/DirichletL/Descent/SecondVaryingPhysical.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u₁ u₂
variable {ι : Type u₁} {σ : Type u₂} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

attribute [local instance] OAI.SevenEighths.InverseMoment.inverseSecondVaryingPhysicalUnits
theorem actual_second_varying_balanced_profile_children
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : MarkedSecondSource ι Jo 0 → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (Real.exp (-6*L):ℂ) * ((Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X))) =
      ((Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹) *
        ∫ t : Frequency × (Fin 6 → ℝ),density t *
          ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,
            (w x*actualSecondSignedWeight p hp hcop hg Ψ
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
            ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
              secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (lists₁ x) (lists₂ x) a₁ a₂
                ω₁ ω₂ G E V B X t := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
