-- Prove2me | Theorems.Thm_HardyLittlewoodMaximal_strongType_real
-- name    : HardyLittlewoodMaximal.strongType_real
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:48:55.839722+00:00
-- url     : https://prove2.me/theorems/3f0038c7-0532-49a6-bdac-bbc01c1e2188
-- title:
--   Theorem A.5.1.1(3) — Hardy–Littlewood maximal theorem on $\mathbb R$: $\|Mf\|_p^p\le\frac{2^p\cdot 3p}{p-1}\|f\|_p^p$ for $p>1$
-- statement:
--   **Hardy–Littlewood maximal theorem on the real line, strong type $(p,p)$.** For a Lebesgue measurable function $f\colon\mathbb R\to\mathbb C$ let
--   $$(Mf)(x)\;=\;\sup_{r>0}\ \frac1{2r}\int_{x-r}^{x+r}|f(y)|\,dy\ \in[0,\infty],\qquad x\in\mathbb R ,$$
--   be its (centred) Hardy–Littlewood maximal function. Let $p>1$ be a real number and let $f\in L^p(\mathbb R,dx)$. Then
--   $$\|Mf\|^p_{L^p(\mathbb R,dx)}=\int_{\mathbb R}(Mf)(x)^p\,dx\;\le\;\frac{2^p\cdot 3\,p}{p-1}\,\|f\|^p_{L^p(\mathbb R,dx)} .$$
--   In particular $Mf\in L^p(\mathbb R,dx)$ and $Mf$ is finite almost everywhere.
--
--   The constant is the one the source derives from the weak type $(1,1)$ inequality with constant $3$. In the source this is the model for the $L^p$ maximal inequalities on locally compact abelian groups (Theorems A.5.3.6 and A.5.3.7).
--
--   **Deviation from the source.** Formula (A.5.1.2) of the source prints the maximal function as a "$\limsup_{r>0}$". The statement, its proof by the covering lemma, and the references given there concern the classical maximal function, which is the supremum over all radii $r>0$; this is what is formalized. Since any upper limit of the averages is bounded by their supremum, the inequality above also holds for the printed formula under every reading of it.
--
--   **Formalization Note.** $Mf$ takes values in $[0,\infty]$ and both sides are integrals of non-negative extended real functions, so no measurability or integrability of $Mf$ has to be assumed to state the inequality; $p$ is a real exponent and $2^p$ a real power. The hypothesis $f\in L^p$ is `MemLp f (ENNReal.ofReal p) volume`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 566, Theorem A.5.1.1(3), eqs. (A.5.1.2) and (A.5.1.4) (proof on p. 567)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace HardyLittlewoodMaximal

theorem strongType_real (f : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x : ℝ, (⨆ (r : ℝ) (_ : 0 < r),
        (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)) ^ p ≤
      ENNReal.ofReal (2 ^ p * 3 * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by sorry

end HardyLittlewoodMaximal
