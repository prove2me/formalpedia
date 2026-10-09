-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondExceptionalKernel_actual_exceptional_block_bound
-- name    : OAI.SevenEighths.CenteredMomentSecondExceptionalKernel.actual_exceptional_block_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:19.831078+00:00
-- url     : https://prove2.me/theorems/21a74975-53c0-41b5-b5cf-841f1a09e5ab
-- title:
--   Exceptional retained blocks bounded by row-polynomial products
-- statement:
--   For a Schwartz $W$ and $\mathrm{decay},J\in\mathbb N$ there is $B\ge0$ such that for every $r>0$, `Character` $\eta$, $t$, finite $S$, $\beta$, `Supported` $C,D$ with equal prime support, $U$, $R$, finite `rows`, reals $\rho,x$ on rows and $u,v$ on the sector pools, $Q\le(72)$, $m$ with `goodLambda`$\mid m$, $2\mid m$, and a ray character $\chi_0$: with $A$ the common·nonunit frequency generator and $c(I)=\beta(CI)$`heightCoeff η t I`, $d(J)=\beta(DJ)$`heightCoeff η t J`, if every row is a `FixedInducingRow (childCharacter η χ₀) Q m A` and $E\ge0$ bounds, for all ray characters $\chi,\xi$ for which the rows are fixed inducing (for $\chi$ at $z$ and $\xi^{-1}$ at $-z$) and all $w$, the sum over $L$ in the divisor pool of $|\mu(L)|\sum_z\|\texttt{rowPolynomial}(\text{left, moving, filtered by }L,\chi)\,z\|\,\|\texttt{rowPolynomial}(\text{right},\xi^{-1})\,(-z)\|$ by $E(1+|w|)^J$, then
--   $$(1+r)^{\mathrm{decay}}\Big\|\sum_{z}\texttt{retainedScalar}\,C\,D\,U\,R\,z\sum_I\sum_J[I,J\text{ coprime}]\,\texttt{idealCorrelation}(CI)(DJ)(Az)\,c(I)\overline{d(J)}\,\texttt{wholeKernel}\,W\,\texttt{logAnnulus}\,r\,\rho_z\,x_z\,u_I\,v_J\Big\|\le B\,E.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondExceptionalKernel.actual_exceptional_block_bound` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondExceptionalKernel.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalKernel
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentMobiusRegroup CenteredMomentFixedRay CenteredMomentRowNorm
open CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentSecondScaled RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSupport CenteredMomentRestrictedEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredExceptionalProfile

theorem actual_exceptional_block_bound (W:𝓢(ℝ,ℂ))(decay J:ℕ):
    ∃B:ℝ,0≤B ∧ ∀r:ℝ,0< r →
      ∀(η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
        (C D:Ideal O)(hC:Supported C)(hD:Supported D),
      primeSupport C=primeSupport D →
      ∀(U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)
        (ρ x:O→ℝ)(u:sectorPool C hC.1 S→ℝ)(v:sectorPool D hD.1 S→ℝ)
        (Q:Ideal O)(m:O)(χ₀:RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c:=fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d:=fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I
      (∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z) →
      ∀E:ℝ,0≤E →
      (∀χ ξ:RayCharacter,
        (∀z∈rows,FixedInducingRow (childCharacter η χ) Q m A z) →
        (∀z∈rows,FixedInducingRow (childCharacter η (ξ⁻¹)) Q m A (-z)) →
        ∀w:ℝ,
        (∑L∈divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
          ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
            (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
              (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) z‖*
          ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
            (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
              (movingCoefficient A (sectorElement D hD.1 S) d) (ξ⁻¹) I*star (columnPhase logAnnulus (v I) w)) (-z)‖)
          ≤E*(1+‖w‖)^J) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤B*E:= by
  sorry

end SevenEighths.CenteredMomentSecondExceptionalKernel

end

end OAI
end
