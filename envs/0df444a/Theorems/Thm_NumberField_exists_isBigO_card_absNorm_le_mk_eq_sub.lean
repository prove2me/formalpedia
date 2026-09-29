-- Prove2me | Theorems.Thm_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub
-- name    : NumberField.exists_isBigO_card_absNorm_le_mk_eq_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/bc5c4858-ea98-5ddc-a8b3-a7fef0f81b38
-- title:
--   Counting ideals in a fixed class, with power saving
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $c$ be an element of the class group $\mathrm{Cl}(\mathcal{O}_K)$ of $\mathcal{O}_K$. The assertion is that there exists a real number $\theta$ with $\theta < 1$ such that the function of a real variable $x$ given by
--   $$\#\{\,I \in (\mathrm{Ideal}\ \mathcal{O}_K)^{0} : \mathrm{absNorm}(I) \le x \text{ and } \mathrm{mk}_0(I) = c\,\} \; - \; \frac{\kappa_K}{h_K}\, x$$
--   is $O(x^{\theta})$ with respect to the filter $\mathrm{atTop}$ on $\mathbb{R}$, i.e. as $x \to \infty$. Here $I$ ranges over the non-zero-divisors of the monoid of ideals of $\mathcal{O}_K$, that is over the non-zero ideals; $\mathrm{absNorm}(I)$ is the absolute norm, compared as a natural number with the real number $x$; $\mathrm{mk}_0(I)$ is the class of $I$ in $\mathrm{Cl}(\mathcal{O}_K)$; the cardinality is the `Nat.card` of the resulting subtype, cast to $\mathbb{R}$; $\kappa_K$ is `NumberField.dedekindZeta_residue K`, the residue at $s = 1$ of the Dedekind zeta function of $K$; and $h_K$ is the class number `NumberField.classNumber K`, cast to $\mathbb{R}$. Only the existence of some exponent $\theta < 1$ is claimed, not a specific value.
--
--   This is the ideal theorem of Weber and Landau in its refinement to a single ideal class: non-zero ideals are equidistributed among the $h_K$ ideal classes, with an error term saving a power of $x$ (classically $\theta = 1 - 1/[K:\mathbb{Q}]$ is admissible). It is used, via partial summation, in [`NumberField.classGroup_eq_closure_nonSplit_degOne`](thm.html#NumberField.classGroup_eq_closure_nonSplit_degOne), where the boundedness as $s \to 1^{+}$ of the partial Dirichlet series $\sum_{[I] = c} N(I)^{-s} - \frac{\kappa_K}{h_K}\frac{1}{s-1}$ is needed; the residue formula for the full zeta function alone gives only $o\bigl((s-1)^{-1}\bigr)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.lean

import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.ClassNumber

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace NumberField
open scoped NumberField nonZeroDivisors

theorem exists_isBigO_card_absNorm_le_mk_eq_sub
    (K : Type*) [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    ∃ (θ : ℝ) (_hθ : θ < 1), (fun x : ℝ =>
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ x
          ∧ ClassGroup.mk0 I = c} : ℝ)
          - (dedekindZeta_residue K / classNumber K) * x)
      =O[Filter.atTop] fun x => x ^ θ := by sorry
