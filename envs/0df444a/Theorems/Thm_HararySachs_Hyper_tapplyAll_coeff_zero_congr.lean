-- Prove2me | Theorems.Thm_HararySachs_Hyper_tapplyAll_coeff_zero_congr
-- name    : HararySachs.Hyper.tapplyAll_coeff_zero_congr
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T04:34:13.214592+00:00
-- url     : https://prove2.me/theorems/34b3e79a-cc85-4ad2-a946-5ce27bbfeca4
-- title:
--   The tensor operator only sees row degrees (k-1)a_i
-- statement:
--   Let $r = k-1$, let $A$ be a rational tensor, and let $a \in \mathbb{N}^n$. Consider the operator $\prod_i f_i(\partial_{V_{i,\cdot}})^{a_i}$ on $\mathbb{Q}[V]$, followed by taking the constant term, where
--   $$f_i(\partial) = \sum_t A_{i,t}\,\partial_{V_{i,t_1}}\cdots\partial_{V_{i,t_r}}.$$
--   This functional only depends on the coefficients of the monomials whose row-$i$ degree $\sum_j \mu_{ij}$ equals $r a_i$ for every $i$. Precisely: if $p, q \in \mathbb{Q}[V]$ and $c \in \mathbb{Q}$ satisfy $[p]_\mu = c\,[q]_\mu$ for all such $\mu$, then the functional takes value $c$ times its value at $q$ when applied to $p$.
--
--   The reason is that each application of $f_i(\partial)$ lowers the row-$i$ degree by exactly $r$, so only those monomials can reach the constant term.
--
--   **Formalization Note** The operator is `tapplyAll A a` and the constant term is `MvPolynomial.coeff 0`.
-- source:
--   Degree bookkeeping for the Morozov–Shakirov operator; mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and 5f345eb5-bd58-46fc-8bd2-52a8bf0241e1.

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- `coeff₀ ∘ tapplyAll A a` only sees the monomials whose row-`i` degree is `(k - 1) a_i`. -/
theorem tapplyAll_coeff_zero_congr {n k d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ)
    (a : Fin n → Fin (d + 1)) (p q : AuxPoly n) (c : ℚ)
    (h : ∀ μ : Fin n × Fin n →₀ ℕ, (∀ i, ∑ j, μ (i, j) = (k - 1) * (a i).val) →
      MvPolynomial.coeff μ p = c * MvPolynomial.coeff μ q) :
    MvPolynomial.coeff 0 (tapplyAll (k := k) A a p) =
      c * MvPolynomial.coeff 0 (tapplyAll (k := k) A a q) := by
  sorry

end HararySachs.Hyper
