-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_row_invariance
-- name    : HararySachs.Hyper.newtonTr_row_invariance
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T21:22:42.087193+00:00
-- url     : https://prove2.me/theorems/b2f1bf1f-9fe6-4a2d-95b7-057a216630f1
-- title:
--   Single-row form of Morozov–Shakirov Proposition I, degree-preserving
-- statement:
--   Let $n \ge 1$, $k \ge 2$ and $r = k-1$, and let $\operatorname{Res}$ be the resultant of $n$ forms of degree $r$ in $n$ variables, normalized by $\operatorname{Res}(x_1^{r},\dots,x_n^{r}) = 1$. Let $V = (V_{jl})$ be an $n \times n$ matrix of indeterminates, and fix a row index $i$.
--
--   Let $A$ be a tensor with entries $A_{j,t} \in \mathbb{Q}[V]$ ($j \in \{1,\dots,n\}$, $t \in \{1,\dots,n\}^r$) such that:
--   1. row $i$ is constant, $A_{i,t} = B_{i,t} \in \mathbb{Q}$;
--   2. no entry of $A$ involves the variables $V_{i1},\dots,V_{in}$ of row $i$.
--
--   Let $A^{(i)}$ be the tensor obtained from $A$ by replacing row $i$ with the power row $A^{(i)}_{i,t} = V_{i t_1}\cdots V_{i t_r}$, so that the $i$-th equation becomes $x_i^{r} - z\,\bigl((Vx)_i\bigr)^{r}$. Write $\tau_d(\cdot)$ for the Newton traces of $\Phi(z) = \operatorname{Res}\bigl(x^{[r]} - z\,\mathcal{A}x^{r}\bigr)$, so that $\log\Phi = -\sum_{d\ge1}\tau_d z^d/d$. Let $\hat f_i = \sum_t B_{i,t}\,\partial_{V_{i t_1}}\cdots\partial_{V_{i t_r}}$, and let $Z_i$ substitute $V_{i1} = \cdots = V_{in} = 0$. Then for every $d \ge 1$,
--   $$\tau_d(A) = \sum_{m=0}^{d} \frac{1}{(rm)!}\, Z_i\Bigl[\hat f_i^{\,m}\,\tau_d\bigl(A^{(i)}\bigr)\Bigr].$$
--
--   This is the single-row form of the Morozov–Shakirov recursion (their Proposition I). It recovers the Newton traces of a system from those of the system in which one equation, $x_i^{r} = f_i(x)$, is replaced by the power equation $x_i^{r} = ((Vx)_i)^{r}$. Unlike the source, all resultants involved have degrees $(r,\dots,r)$. Applying it once per row, the rows can be replaced one at a time; this gives the generalized Proposition II (`newtonTr_eq_operator`).
--
--   **Formalization Note** The entries live in `AuxPoly n` $= \mathbb{Q}[V]$. Hypothesis 2 is stated through `MvPolynomial.vars`. $Z_i$ is `MvPolynomial.aeval` with $V_{jl} \mapsto 0$ for $j = i$ and $V_{jl} \mapsto V_{jl}$ otherwise. $\hat f_i$ is `tfhat B i`, and $A^{(i)}$ is `Function.update A i (fun t => ∏ s, X (i, t s))`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 3, Proposition I and eq. (15), in the variant that replaces the linear equation $x_1 - v\cdot x$ by $x_1^{k-1} - (v\cdot x)^{k-1}$ (mission strategy comments 2173f2a9-fd2e-4d5e-afb5-27607d970161 and 8357894d-0c47-45af-94e5-d71263b245a7).

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

theorem newtonTr_row_invariance (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (A : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n)
    (B : Fin n → (Fin (k - 1) → Fin n) → ℚ) (i : Fin n)
    (hAi : ∀ t, A i t = MvPolynomial.C (B i t))
    (hfree : ∀ j t, ∀ v ∈ (A j t).vars, v.1 ≠ i)
    (d : ℕ) (hd : 1 ≤ d) :
    newtonTr (phiPoly (k := k) A res) d =
      ∑ m : Fin (d + 1), (1 / (Nat.factorial (m.val * (k - 1)) : ℚ)) •
        MvPolynomial.aeval
          (fun v : Fin n × Fin n => if v.1 = i then (0 : AuxPoly n) else MvPolynomial.X v)
          ((tfhat (k := k) B i)^[m.val]
            (newtonTr (phiPoly (k := k)
              (Function.update A i (fun t => ∏ s, MvPolynomial.X (i, t s))) res) d)) := by sorry

end HararySachs.Hyper
