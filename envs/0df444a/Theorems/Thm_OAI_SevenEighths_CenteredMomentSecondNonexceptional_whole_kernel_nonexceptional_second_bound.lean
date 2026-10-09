-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondNonexceptional_whole_kernel_nonexceptional_second_bound
-- name    : OAI.SevenEighths.CenteredMomentSecondNonexceptional.whole_kernel_nonexceptional_second_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:17:31.407327+00:00
-- url     : https://prove2.me/theorems/b7cfe59e-f029-4781-9c57-07a6a71bc945
-- title:
--   Nonexceptional second correlation sums bounded by restricted energies
-- statement:
--   Let $W$ be Schwartz, $V:\mathrm{Fin}\,4\to\mathbb R\to\mathbb C$ with $V_i(y)\ne0\Rightarrow|y|\le M_i$ ($M_i\ge0$), and $A,J_1,J_2\in\mathbb N$. Then there is $C\ge0$ such that for every $R>0$, finite `rows` of Eisenstein integers, finite index sets $S,T$, `Supported` elements $D,E$, $a_i$, $b_j$, all $\equiv1\bmod$ `goodLambda`$^2$, with $DE$ coprime to every $a_i,b_j$; coefficients $q,c,d$, reals $u,v,\rho,x$, a `HeckeFamily.Character` $\eta_0$, a ray character $\chi_0$, an ideal $Q\le(72)$ and $m$ with `goodLambda`$\mid m$, $2\mid m$; with every row `nonexceptional η₀ χ₀ Q m A₀`, $|q(z)\,$`actualCorrelation D E (A₀z)`$|\le1$, $|V_0(\rho_z)|,|V_1(x_z)|\le1$ on rows; a Schwartz $U$ and $K>0$ with $\operatorname{Re}U(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$ everywhere and $\ge1$ on rows; and nonnegative $B_1,B_2$ on `divisorPool T b` such that, for every $L$ there, every ray character and every $t$, the `restrictedEnergy` of the left coefficients (`divisorCoefficient L a (movingCoefficient A₀ a c) χ`·`columnPhase (V 2) (u i) t`) is at most $(B_1(L)(1+|t|)^{J_1})^2$ and that of the right ones (with $\overline{\texttt{columnPhase}\,(V\,3)\,(v_j)\,t}$) at most $(B_2(L)(1+|t|)^{J_2})^2$:
--   $$(1+R)^A\Big\|\sum_{z\in\mathrm{rows}}q(z)\sum_{i\in S}\sum_{j\in T}[a_i,b_j\text{ coprime}]\,\texttt{actualCorrelation}(Da_i,Eb_j,A_0z)\,c_i\overline{d_j}\,\texttt{wholeKernel}\,W\,V\,R\,\rho_z\,x_z\,u_i\,v_j\Big\|\le C\sum_{L}|\mu(L)|\,B_1(L)B_2(L).$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondNonexceptional.whole_kernel_nonexceptional_second_bound` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondNonexceptional.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptional
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth RayFourExpansion
open CenteredMomentSecondScaled CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem whole_kernel_nonexceptional_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η₀ : HeckeFamily.Character) (χ₀ : RayCharacter)
        (Q : Ideal O) (m : O),
      (Q ≤ Ideal.span {(72:O)}) → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ z ∈ rows, nonexceptional η₀ χ₀ Q m A₀ z) →
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ χ Q m A₀) S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K) ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ ξ Q m A₀) T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K) ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  sorry

end SevenEighths.CenteredMomentSecondNonexceptional

end

end OAI
end
