-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseInitialEnergyCallerIntegral_actual_common_integral_bound
-- name    : OAI.SevenEighths.InverseInitialEnergyCallerIntegral.actual_common_integral_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:53:21.003131+00:00
-- url     : https://prove2.me/theorems/82247e28-542b-4e99-87fb-71ff1eb5d98c
-- title:
--   Integrated row-mode bound from column-energy moments
-- statement:
--   For every $N\in\mathbb N$, $U\ge0$ and $\pi>0$ there is $C>0$ such that the following holds. Let $p:\iota\to\mathcal O$ be a family of nonzero Eisenstein integers (`ActualEisensteinCubic.O`) generating maximal, pairwise coprime, distinct ideals that avoid `goodLambda`, with `goodLambda`$^2\mid p_i-1$ and residue characteristic $\ne2$. Let $S$ be a finite set of `Source 0` points whose divisor lies in their common part, `pool` finite, $\Psi$ multiplicative bounded by 1, $j\in\mathcal O$, at most $N$ `slots` with `lists` and coefficients $a$ bounded by 1, $\omega_1,\omega_2:\mathbb R\to\mathbb C$, reals $Z\ge1$, $D,B,v,\theta,H$ and $R\le U$ with every ideal of `quotientSet p S` of norm $\le Z^R$, weights $w$ bounded by 1 on $S$, finite sets `labels` (nonzero ideals) and `rows` (closed under negation) containing the `initialChild` label and row of every point of $S$, reals $F$ and $A\ge0$, $J\in\mathbb N$, Schwartz functions $g:\mathrm{Fin}\,6\to\mathcal S$, $g_1,g_2,b_3$ and reals $c_1,c_2,\theta_1,\theta_2,L$. If for every frequency $z$, ray index $\rho$, subsets $J_1,J_2$ of `slots` and $t$ in `quotientSet p S`, both `normalizedColumnEnergy` values (for `secondRayMinus Ψ ρ` with `childLogTest ω₁` and for `secondRayPlus Ψ ρ` with `childLogTest ω₂`, at the `profileHeight` coordinates 4 and 5, centre $Z^{\texttt{columnCenter}\,D\,B\,v}$) are at most $A\cdot$`tripleHeight J z.1`$\cdot$`coordinateHeight J z.2`, then
--   $$\Big\|\int\texttt{familyDensity}(\dots)(z)\sum_{x\in S}\sum_{\rho}w(x)\,\texttt{rowMode}(\dots,x,\rho,z)\,dz\Big\|\le C\,Z^{F+R+\pi}A\int\texttt{tripleHeight}\,J\,z_1\,\texttt{coordinateHeight}\,J\,z_2\,\|\texttt{familyDensity}(\dots)(z)\|\,dz.$$
--
--   Lean: `OAI.SevenEighths.InverseInitialEnergyCallerIntegral.actual_common_integral_bound` in `lean/OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCallerIntegral.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B012

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerIntegral
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation
open InverseInitialQuotientGeometry InverseInitialClippedColumns
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_common_integral_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A:ℝ)(_hA:0≤A)(J:ℕ)
      (g:Fin 6→𝓢(ℝ,ℂ))(g₁ g₂ b₃:𝓢(ℝ,ℂ))(c₁ c₂ θ₁ θ₂ L:ℝ)
      (_hmoment:∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2)),
      ‖∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
        familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z*
        (∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
          Z D B v θ H x ρ z)‖≤
        C*Z^(F+R+π)*A*(∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
          tripleHeight J z.1*coordinateHeight J z.2*‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
  sorry

end SevenEighths.InverseInitialEnergyCallerIntegral

end

end OAI
end
