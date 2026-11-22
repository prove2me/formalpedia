-- Prove2me | Theorems.Thm_HardyLittlewoodMaximal_weakType_one_one_real
-- name    : HardyLittlewoodMaximal.weakType_one_one_real
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:48:53.848917+00:00
-- url     : https://prove2.me/theorems/648dc8fc-6be5-46ff-bed9-3a31019e3aeb
-- title:
--   Theorem A.5.1.1(2) — Hardy–Littlewood maximal theorem on $\mathbb R$: weak type $(1,1)$ with constant $3$
-- statement:
--   **Hardy–Littlewood maximal theorem on the real line, weak type $(1,1)$.** For a Lebesgue measurable function $f\colon\mathbb R\to\mathbb C$ the (centred) Hardy–Littlewood maximal function of $f$ is
--   $$(Mf)(x)\;=\;\sup_{r>0}\ \frac1{2r}\int_{x-r}^{x+r}|f(y)|\,dy\ \in[0,\infty],\qquad x\in\mathbb R .$$
--   Let $f\in L^1(\mathbb R,dx)$. Then for every real number $\alpha>0$
--   $$\big|\{x\in\mathbb R:\ (Mf)(x)>\alpha\}\big|\;\le\;\frac{3}{\alpha}\,\|f\|_{L^1(\mathbb R,dx)},$$
--   where $|\cdot|$ is Lebesgue measure.
--
--   This is the weak type $(1,1)$ estimate; the constant $3$ is the one produced by the Vitali covering lemma in dimension one. In the source it is the model case for the maximal theorems on idele groups and idele class groups, and the input for Lebesgue's differentiation theorem (Theorem A.5.1.3).
--
--   **Deviation from the source.** Formula (A.5.1.2) of the source prints the maximal function as a "$\limsup_{r>0}$". The statement, its proof by the covering lemma, and the references given there concern the classical maximal function, which is the supremum over all radii $r>0$; this is what is formalized. Since any upper limit of the averages is bounded by their supremum, the inequality above also holds for the printed formula under every reading of it.
--
--   **Formalization Note.** The averages are integrals of the non-negative extended real function $|f|$ over the open interval $(x-r,x+r)$, divided by $2r$, so that $Mf$ takes values in $[0,\infty]$; the superlevel set is $\{x:\ \alpha<(Mf)(x)\}$ with $\alpha$ embedded by `ENNReal.ofReal`, and $\|f\|_{L^1}$ is $\int|f|$ as an extended real.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 566, Theorem A.5.1.1(2), eqs. (A.5.1.2)-(A.5.1.3) (proof on p. 567); classical reference: E. M. Stein and R. Shakarchi, Real Analysis. Measure Theory, Integration and Hilbert Spaces, Princeton Lectures in Analysis III, 2005, Ch. 3, §1, Thm. 1.1(iii), p. 101 (as cited in the paper's proof)

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace HardyLittlewoodMaximal

theorem weakType_one_one_real (f : ℝ → ℂ) (hf : Integrable f volume) (α : ℝ) (hα : 0 < α) :
    volume {x : ℝ | ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)} ≤
      ENNReal.ofReal (3 / α) * ∫⁻ x, ‖f x‖ₑ := by sorry

end HardyLittlewoodMaximal
