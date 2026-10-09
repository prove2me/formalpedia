-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_second_deleted_moving_physical_recursive_uniform_types
-- name    : OAI.SevenEighths.InverseMoment.actual_second_deleted_moving_physical_recursive_uniform_types
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:33.7503+00:00
-- url     : https://prove2.me/theorems/fc50b044-0790-47e2-a57d-1800d388a585
-- title:
--   Deleted second rows bounded through column energies, uniformly in the types
-- statement:
--   Let $U_0:\mathrm{Fin}\,6\to\mathcal S(\mathbb R)$, $g_1,g_2,\Phi$ Schwartz, $M_0,B_0\ge0$ on $\mathrm{Fin}\,6$, reals $m_1,m_2,b_{\mathrm{cap}}$ with $U_0(i)$ supported in $[-M_0(i),M_0(i)]$ and $g_k$ in $[-m_k,m_k]$, and $A_{\mathrm{ker}},J\in\mathbb N$. Then there is $C\ge0$ such that for every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` with `goodLambda`$^2\mid p_i-1$ and residue characteristic $\ne2$, every finite `source` of `MarkedSecondSource ι Jo 0` with `ActualSecondSourceConditions`, `pool`, $\Psi$ bounded by 1, $m$, $z$, two slot systems with coefficients bounded by 1 and at most $K$ slots ($J_o\le2K$), deleted sets as in the companion statement, $\omega_1,\omega_2$, reals $G,E,V,B,Y>0$, $Z>0$, $Z^N>0$, $R$, $L\ge0$, `Vlabel`, $\varepsilon_{\mathrm{child}}$, $\rho$ with $|\rho_i|\le B_0(i)$, $1\le c_1,c_2\le b_{\mathrm{cap}}$, $\theta_1,\theta_2$, weights $w$ bounded by 1, a finite set `labels` containing every child label, and $A\ge0$ — assuming the second frequencies lie in `nonzeroChildFrequencyBall`, that $\omega_1,\omega_2$ equal 1 where the `positiveSource` profiles are nonzero, that every $U_0(i)$ equals 1 at the shifted `secondRelativeLog` coordinates of `secondProfileIndices`, and the two `normalizedColumnEnergy` bounds (by $A\,Z^{\max(0,N)+\mathrm{Vlabel}+\varepsilon_{\mathrm{child}}}$ times `tripleHeight J`·`coordinateHeight J`) — the norm of $Y\cdot$`secondRayCoefficient z` times $\sum_xw(x)\,$`actualSecondSignedWeight`·`actualSecondProfileRow` (with tests $\overline{\texttt{positiveSource}\,g_1\,c_1\,\theta_1}$ and `positiveSource g₂ c₂ θ₂`, scale $GVZ^N$) is at most
--   $$e^{6L}\Big\|\frac{Y\,\texttt{secondRayCoefficient}\,z}{EVZ^N}\Big\|\cdot36\cdot2^{|\mathrm{slots}_1|+|\mathrm{slots}_2|}A\,Z^{2(\max(0,N)+\mathrm{Vlabel})+\varepsilon_{\mathrm{child}}}\sum_{\gamma}\texttt{tripleDivisorWeight}\,K\,\gamma\cdot\frac{C(1+|\theta_1|)^k(1+|\theta_2|)^k}{(1+YB/(EV^2Z^{2N}))^{A_{\mathrm{ker}}}},$$
--   $\gamma$ over `actualSecondTriples p 1 1 source`, $k=$`momentOrder J`.
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_second_deleted_moving_physical_recursive_uniform_types` in `lean/OAI/NumberTheory/DirichletL/Descent/SecondDeletedMovingEnergyUniform.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseSecondProfileUniform InverseAmbientProfileTower
theorem actual_second_deleted_moving_physical_recursive_uniform_types
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
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
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
