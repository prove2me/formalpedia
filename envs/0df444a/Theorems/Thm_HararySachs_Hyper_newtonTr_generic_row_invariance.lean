-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_generic_row_invariance
-- name    : HararySachs.Hyper.newtonTr_generic_row_invariance
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T03:02:06.721565+00:00
-- url     : https://prove2.me/theorems/d556e0fb-638d-492d-a453-b54a745e52b4
-- title:
--   Row invariance of the Newton traces for the generic tensor
-- statement:
--   Let $n \ge 1$, $k \ge 2$ and $r = k-1$, and let $\operatorname{Res}$ be the resultant of $n$ forms of degree $r$ in $n$ variables, normalized by $\operatorname{Res}(x_1^r,\dots,x_n^r) = 1$. Let $\mathbb{A}$ be the generic tensor, whose entries $X_{j,t}$ are independent indeterminates over $\mathbb{Q}$. Let $\tau_d(\mathbb{A})$ be the Newton traces of
--   $$\Phi(z) = \operatorname{Res}\bigl(x^{[r]} - z\,\mathbb{A}x^{r}\bigr), \qquad \log\Phi(z) = -\sum_{d \ge 1}\frac{\tau_d}{d}\,z^d.$$
--   Fix a row $i$. Let $\mathbb{A}'$ be the tensor obtained by replacing every $X_{i,t}$ with the monomial $v_{t_1}\cdots v_{t_r}$ in new variables $v$, keeping the other entries as coefficients. Let $f_i(\partial_v) = \sum_t X_{i,t}\,\partial_{v_{t_1}}\cdots\partial_{v_{t_r}}$. Then for every $d \ge 1$,
--   $$\tau_d(\mathbb{A}) = \sum_{m=0}^{d} \frac{1}{(rm)!}\Bigl[f_i(\partial_v)^{m}\,\tau_d(\mathbb{A}')\Bigr]_{v=0}.$$
--
--   This is the generic form of the single-row Morozov–Shakirov identity: the Newton traces are fixed by the row projection $\Pi_i$. The statement for arbitrary tensors with entries in $\mathbb{Q}[V]$ (`newtonTr_row_invariance`) follows by substituting the entries for the indeterminates.
--
--   **Formalization Note** The coefficient ring is `MvPolynomial (Fin n × (Fin (k-1) → Fin n)) ℚ` and the variables $v$ are those of `MvPolynomial (Fin n)` over it. The bracket is `MvPolynomial.eval 0`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 3, Proposition I, in the degree-preserving variant of mission strategy comments 2173f2a9-fd2e-4d5e-afb5-27607d970161 and 8357894d-0c47-45af-94e5-d71263b245a7.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

theorem newtonTr_generic_row_invariance (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (i : Fin n) (d : ℕ) (hd : 1 ≤ d) :
    newtonTr (phiPoly (k := k)
        (fun j t => (MvPolynomial.X (j, t) :
          MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ)) res) d =
      ∑ m : Fin (d + 1), (1 / (Nat.factorial (m.val * (k - 1)) : ℚ)) •
        MvPolynomial.eval 0
          ((fun p : MvPolynomial (Fin n) (MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ) =>
              ∑ t : Fin (k - 1) → Fin n, (MvPolynomial.X (i, t) :
                MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ) •
                (List.ofFn t).foldr (fun j q => MvPolynomial.pderiv j q) p)^[m.val]
            (newtonTr (phiPoly (k := k)
              (fun j t => if j = i then ∏ s, MvPolynomial.X (t s)
                else MvPolynomial.C (MvPolynomial.X (j, t))) res) d)) := by sorry

end HararySachs.Hyper
