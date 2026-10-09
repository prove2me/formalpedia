-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_first_family_two_energies
-- name    : OAI.SevenEighths.InverseMoment.actual_first_family_two_energies
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T22:00:29.83487+00:00
-- url     : https://prove2.me/theorems/19725dd3-812a-4afa-b652-243df1369365
-- title:
--   First-family physical rows bounded by two energies
-- statement:
--   Let $\iota,\kappa$ be types ($\iota$ with decidable equality), $p:\iota\to\mathcal O$ a family of nonzero elements of the Eisenstein integers (`ActualEisensteinCubic.O`) generating maximal ideals none of which contains `ConcretePrimeRowBridge.goodLambda` (witness `hg`). Let `source` be a finite set of $\kappa$, $F$ a finite set of $\iota$, `selector`, $C_1,C_2:\kappa\to\mathrm{Finset}\,\iota\to\mathbb C$, $w:\kappa\to\mathbb C$, $W_1,W_2,\omega_1,\omega_2:\mathbb R\to\mathbb C$, $\Phi$ a Schwartz function, $V:\mathrm{Fin}\,9\to\mathbb R\to\mathbb C$, $A_1,A_2,C,R:\kappa\to\mathbb R$, $K,L\in\mathbb R$, $d,h:\kappa\to\mathcal O$ and $s:\mathrm{Fin}\,9\to\mathbb R$ with all $s_i>0$; for $x$ in `source`, $A_1(x),A_2(x),C(x),R(x)>0$ and $d(x),h(x)\neq0$. Assume: a density on `Frequency × (Fin 9 → ℝ)` is integrable and represents $e^{-9L/2}$ times `firstPoissonProfile W₁ W₂ Φ V` (at scale $Ks_6/(s_3s_4s_5^2s_7s_8)$) as an integral of `pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope`; the cutoffs $\omega_1,\omega_2$ equal $1$ and the $V_i$ equal $1$ (at `firstRelativeLog` of `firstCommonNorms`) on every index of `firstCommonIndices F` contributing a nonzero term (hypotheses `hω₁`, `hω₂`, `hcut`, phrased with `firstCommonWeight` and `primeProductNorm`); and for $J\in\mathbb N$ and $B_1,B_2\ge0$, the density weighted by `tripleHeight J`·`coordinateHeight J` is integrable and the left and right `firstFamilyEnergy` values at `profileHeight` coordinates 7 and 8 are at most $B_1$, respectively $B_2$, times that weight. Then
--   $$\|\texttt{firstFamilyPhysicalRows}\ \dots\|\le\frac{e^{9L/2}}{\texttt{firstRootScale}\,s}\sqrt{B_1}\sqrt{B_2}\int\texttt{tripleHeight}\,J\,z_1\cdot\texttt{coordinateHeight}\,J\,z_2\cdot\|\mathrm{density}(z)\|\,dz.$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_first_family_two_energies` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstUnequalPhysicalEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B006

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_first_family_two_energies (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hWeighted : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
