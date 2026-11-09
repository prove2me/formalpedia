-- Prove2me | Theorems.Thm_GevreyGibbsSep_lemma_B_7
-- name    : GevreyGibbsSep.lemma_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:06.848291+00:00
-- url     : https://prove2.me/theorems/0d25d2b4-35d3-4853-9b73-6174baa34d7a
-- title:
--   Lemma B.7 — Gevrey-like bound for composition with $\log$
-- statement:
--   Let $\Omega\subseteq\mathbb R^d$ be open and $h\in C^\infty(\Omega,\mathbb R^+)$ such that, for some $s\ge1$, $K>0$, $R>0$,
--   $$|\partial^ah(x)|\le K\big(\|a\|_1!\big)^sR^{\|a\|_1}h(x)\qquad\forall a\in\mathbb N^d\setminus\{0\},\ x\in\Omega .$$
--   Then $F=\log h$ satisfies
--   $$|\partial^aF(x)|\le\frac{K}{1+K}\big(\|a\|_1!\big)^s\big((1+K)R\big)^{\|a\|_1}\qquad\forall a\in\mathbb N^d\setminus\{0\},\ x\in\Omega .$$
--   Here $\|a\|_1!$ is the factorial of the total order. The lemma transfers Gevrey bounds from the bump density to its potential.
--
--   Differences from the source:
--   - encoding: $\partial^a$ of $h$ and $\log h$ on $\Omega$ → iterated coordinate Fréchet derivatives of functions on $\mathbb R^d$, evaluated at points of the open set $\Omega$; reason: at interior points these are the derivatives of the restrictions to $\Omega$
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Lemma B.7, Eqs. (B59)–(B60), p.44

import Mathlib
import Definitions.Def_GevreyGibbsSep_partialDeriv

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Lemma B.7 (Gevrey-like bound for composition with log), arXiv:2608.24527 (sha256 d4fd40eb…),
Eqs. (B59)–(B60), p.44. Let `Ω ⊆ ℝ^d` be open and `h ∈ C^∞(Ω, ℝ⁺)` with
`|∂^a h(x)| ≤ K (‖a‖₁!)^s R^{‖a‖₁} h(x)` for all `a ≠ 0`, `x ∈ Ω`, where `s ≥ 1`, `K, R > 0`. Then
`F = log h` satisfies `|∂^a F(x)| ≤ (K/(1 + K)) (‖a‖₁!)^s ((1 + K)R)^{‖a‖₁}` for all `a ≠ 0`,
`x ∈ Ω`. (Here `‖a‖₁!` is the factorial of the total order, not `a!`.) -/
theorem lemma_B_7 {d : ℕ} (Ω : Set (Fin d → ℝ)) (hΩ : IsOpen Ω) (h : (Fin d → ℝ) → ℝ)
    (hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h Ω) (hpos : ∀ x ∈ Ω, 0 < h x)
    (s K R : ℝ) (hs : 1 ≤ s) (hK : 0 < K) (hR : 0 < R)
    (hyp : ∀ a : Fin d → ℕ, a ≠ 0 → ∀ x ∈ Ω,
      |partialDeriv a h x| ≤ K * ((∑ i, a i).factorial : ℝ) ^ s * R ^ (∑ i, a i) * h x) :
    ∀ a : Fin d → ℕ, a ≠ 0 → ∀ x ∈ Ω,
      |partialDeriv a (fun y => Real.log (h y)) x|
        ≤ K / (1 + K) * ((∑ i, a i).factorial : ℝ) ^ s * ((1 + K) * R) ^ (∑ i, a i) := by sorry

end GevreyGibbsSep
