-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_3_2
-- name    : OrderSelProphet.Kernel.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:14.132557+00:00
-- url     : https://prove2.me/theorems/ae44278a-1235-4c28-ad5d-e42c86421d15
-- title:
--   Lemma 3.2 — profile–area correspondence: $\lambda\mapsto A_\lambda$ is a bijection $\Lambda\to\mathcal A$, with (13), (14) and the properties of $x_\lambda$
-- statement:
--   There is a bijection $\Lambda\to\mathcal A$, $\lambda\mapsto A_\lambda$ (with $A_\lambda$ given by (38)), such that for every input and every item $i$ the profile $\lambda_i$ corresponds to the area curve $A_i$. In particular $A_\lambda=A_{\tilde\lambda}\iff\lambda=\tilde\lambda$ a.e., and $A_\lambda(1)=\int_0^1\lambda$. For $\lambda\in\Lambda$ and $0\le u<1$, with $h_\lambda,C_\lambda,x_\lambda,\mu_\lambda$ as in (12): $x_\lambda$ is continuous and nondecreasing with $0\le x_\lambda(u)\le u$, and
--   $$A_\lambda(x_\lambda(u))=C_\lambda(u)-(1-u)(e^{h_\lambda(u)}-1)=C_\lambda(u)+x_\lambda(u)-u.\quad(13)$$
--   With $x^*=\lim_{u\uparrow1}x_\lambda(u)$: if $x^*<1$ then $A_\lambda(x)=\mu_\lambda+x-1$ on $[x^*,1]$ (14). Together with continuity and $A_\lambda(1)=\mu_\lambda$ these formulas determine $A_\lambda$ on $[0,1]$.
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: 𝒜: area curves of items of inputs (n ≥ 2) → AreaClass: restrictions to [0,1] of A_i for atomless inputs with n ≥ 1; reason: the n = 1 curve A(x) = x is also item 1's curve in the two-item input with profiles (1, 0), so the class is the same
--   - encoding: a bijection Λ → 𝒜 (a.e. classes) → three clauses: A_λ ∈ 𝒜 for every profile; every A ∈ 𝒜 is some A_λ; A_λ = A_λ' on [0,1] ⟺ λ = λ' a.e. on [0,1]; reason: this is a bijection from a.e. classes onto 𝒜
--   - encoding: 'for every input and item i, the profile λ_i corresponds to A_i' → every item of an atomless input has a profile, and A_i = A_λ on [0,1] for every profile λ of item i; reason: the existence of λ_i is asserted on p. 9 (definition (10))
--   - encoding: x* := lim_{u↑1} x_λ(u); 'these formulas determine A_λ on [0,1]' → ∃ x*, x_λ → x* as u ↑ 1 with (14) when x* < 1; every A' continuous on [0,1] with A'(1) = μ_λ satisfying (13) and (14) equals A_λ on [0,1]; reason: the limit exists by monotonicity; 'determine' read as uniqueness among continuous functions
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma 3.2, p. 10 (proof in Appendix B.5, p. 42)

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Profiles

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma 3.2 (Profile–area correspondence), p. 10 (proof in Appendix B.5, p. 42). -/
theorem lemma_3_2 :
    (∀ lam : Profile, onUnit (areaP lam.1) ∈ AreaClass) ∧
      (∀ A ∈ AreaClass, ∃ lam : Profile, onUnit (areaP lam.1) = A) ∧
      (∀ lam lam' : Profile, onUnit (areaP lam.1) = onUnit (areaP lam'.1) ↔
        lam.1 =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] lam'.1) ∧
      (∀ (n : ℕ) (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)], IsAtomlessInput F →
        ∀ i, (∃ lam : Profile, IsProfileOf F i lam.1) ∧
          ∀ lam : Profile, IsProfileOf F i lam.1 → onUnit (inputArea F i) = onUnit (areaP lam.1)) ∧
      ∀ lam : Profile,
        areaP lam.1 1 = muP lam.1 ∧
        ContinuousOn (xP lam.1) (Ico 0 1) ∧ MonotoneOn (xP lam.1) (Ico 0 1) ∧
        (∀ u ∈ Ico (0 : ℝ) 1, 0 ≤ xP lam.1 u ∧ xP lam.1 u ≤ u) ∧
        (∀ u ∈ Ico (0 : ℝ) 1,
          areaP lam.1 (xP lam.1 u) = CP lam.1 u - (1 - u) * (Real.exp (hP lam.1 u) - 1) ∧
            areaP lam.1 (xP lam.1 u) = CP lam.1 u + xP lam.1 u - u) ∧
        (∃ xs : ℝ, Tendsto (xP lam.1) (𝓝[<] 1) (𝓝 xs) ∧
          (xs < 1 → ∀ x ∈ Icc xs 1, areaP lam.1 x = muP lam.1 + x - 1)) ∧
        ∀ A' : ℝ → ℝ, ContinuousOn A' (Icc 0 1) → A' 1 = muP lam.1 →
          (∀ u ∈ Ico (0 : ℝ) 1, A' (xP lam.1 u) = CP lam.1 u + xP lam.1 u - u) →
          (∀ xs : ℝ, Tendsto (xP lam.1) (𝓝[<] 1) (𝓝 xs) → xs < 1 →
            ∀ x ∈ Icc xs 1, A' x = muP lam.1 + x - 1) →
          EqOn A' (areaP lam.1) (Icc 0 1) := by sorry

end OrderSelProphet.Kernel
