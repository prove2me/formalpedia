-- Prove2me | Theorems.Thm_HararySachs_Hyper_generic_row_points
-- name    : HararySachs.Hyper.generic_row_points
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T03:01:58.423604+00:00
-- url     : https://prove2.me/theorems/ddd43387-acf2-43bd-a104-67c113a154aa
-- title:
--   Genericity certificate: the other rows have the full set of normalized common zeros
-- statement:
--   Let $n \ge 1$, $k \ge 2$, $r = k-1$, let $\operatorname{Res}$ be the normalized resultant of $n$ forms of degree $r$, and fix a row $i$. For a complex tensor $a$, let
--   $$F_j^a(x) = x_j^{r} - \sum_t a_{j,t}\,x_{t_1}\cdots x_{t_r} \qquad (j = 1,\dots,n).$$
--   Then there is a nonzero polynomial $\Delta$ in the entries of $a$ with the following property. Whenever $\Delta(a) \ne 0$:
--   1. there are $(k-1)^{n-1}$ distinct points $p \in \mathbb{C}^n$ with $p_i = 1$ that are common zeros of $F_j^a$ for all $j \ne i$;
--   2. the resultant of the system obtained by replacing $F_i^a$ with $x_i^{r}$ is nonzero.
--
--   Condition 2 says that the other equations have no common zero on the hyperplane $x_i = 0$. Together with condition 1 it says that they are in general position: their common zeros are $(k-1)^{n-1}$ distinct points, all off that hyperplane. This is the hypothesis under which Poisson's product formula takes its simple form, and since $\Delta \ne 0$ it holds on a Zariski-dense set.
--
--   **Formalization Note** The conclusion is stated with explicit forms `X j ^ (k-1) - ∑ t, C (a (j,t)) * ∏ s, X (t s)`; the resultant in condition 2 is the evaluation of `res` at the coefficients of the system with row $i$ replaced by `X i ^ (k-1)`.
-- source:
--   Bezout count for $n-1$ forms of degree $k-1$ in $n$ variables, used in the Poisson product formula of Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 3 ("suppose that this system is in general position").

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

namespace HararySachs.Hyper

theorem generic_row_points (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) :
    ∃ Δ : MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℂ, Δ ≠ 0 ∧
      ∀ a : Fin n × (Fin (k - 1) → Fin n) → ℂ, MvPolynomial.eval a Δ ≠ 0 →
        (∃ P : Finset (Fin n → ℂ), P.card = (k - 1) ^ (n - 1) ∧
          ∀ p ∈ P, p i = 1 ∧ ∀ j, j ≠ i →
            MvPolynomial.eval p (MvPolynomial.X j ^ (k - 1) -
              ∑ t : Fin (k - 1) → Fin n,
                MvPolynomial.C (a (j, t)) * ∏ s, MvPolynomial.X (t s)) = 0) ∧
        MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
            MvPolynomial.coeff v.2.1 (Function.update
              (fun j => MvPolynomial.X j ^ (k - 1) -
                ∑ t : Fin (k - 1) → Fin n,
                  MvPolynomial.C (a (j, t)) * ∏ s, MvPolynomial.X (t s))
              i (MvPolynomial.X i ^ (k - 1)) v.1))
          (MvPolynomial.map (Int.castRingHom ℂ) res) ≠ 0 := by sorry

end HararySachs.Hyper
