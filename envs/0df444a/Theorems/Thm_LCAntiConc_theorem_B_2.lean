-- Prove2me | Theorems.Thm_LCAntiConc_theorem_B_2
-- name    : LCAntiConc.theorem_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:15.805484+00:00
-- url     : https://prove2.me/theorems/e652450b-0719-41c0-9f3e-247ce2d4e923
-- title:
--   Theorem B.2 — finite-time Stein kernel: a $(T,e^{-T/C})$-approximate Stein kernel for smooth isotropic log-concave laws
-- statement:
--   Let $X\in\mathbb R^d$ be an isotropic log-concave random vector with a smooth density, that is, with density $e^{-W}$ where $W:\mathbb R^d\to\mathbb R$ is smooth, convex, and has bounded Hessian. There is an absolute constant $C$ (independent of $d$ and of $X$) such that for every $T\ge1$, $X$ has a $(T,e^{-T/C})$-bounded approximate Stein kernel in the sense of Definition B.1, with constant $C$ in (B.3).
--
--   The kernel is a truncation at time $T$ of the Langevin-semigroup construction of Courtade, Fathi and Pananjady; the dimension-free bound comes from the KLS theorem (Fact 3.1).
--
--   Differences from the source:
--   - reading: "an absolute constant C" for the (T, e^{-T/C}) kernel, with the O(·) of (B.3) unspecified → one absolute constant C, also used as the (B.3) constant, quantified before d and the law; reason: every O(·) of the paper is universal (p.27); one constant for several is equivalent
--   - encoding: smooth W with bounded Hessian → ContDiff ℝ ∞ W and ∃ M, ∀ x, ‖D²W(x)‖ ≤ M; reason: C^∞ smoothness; a uniform bound on the second derivative
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Theorem B.2, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_LCAntiConc_IsIsotropic
import Definitions.Def_LCAntiConc_IsStein

namespace LCAntiConc

open MeasureTheory

/-- **Theorem B.2** (Finite-time Stein kernel). Let `X ∈ ℝ^d` be an isotropic log-concave random
vector with a smooth density, i.e., with density `e^{-W}`, where `W` is smooth, convex, and has
bounded Hessian. There is an absolute constant `C` such that for every `T ≥ 1`, `X` has a
`(T, e^{-T/C})`-approximate Stein kernel in the sense of Definition B.1.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Theorem B.2, p.45 (PDF p.47).

**Formalization Note** "Smooth" is `C^∞` (`ContDiff ℝ (⊤ : ℕ∞)`); "bounded Hessian" is a uniform
bound on the second derivative `D²W`. The absolute constant `C` also serves as the `O(·)` in (B.3)
of the kernel, and it comes before `d` and the law. -/
theorem theorem_B_2 :
    ∃ C > 0, ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d)))
      (W : EuclideanSpace ℝ (Fin d) → ℝ),
      IsIsotropic μ → μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-W x))) →
      ContDiff ℝ (⊤ : ℕ∞) W → ConvexOn ℝ Set.univ W →
      (∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 W x‖ ≤ M) →
      ∀ T : ℝ, 1 ≤ T → ∃ (H : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
        (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        IsStein μ T (Real.exp (-T / C)) C H r := by sorry

end LCAntiConc
