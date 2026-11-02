-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_lemma_6_2_a
-- name    : OblivEllipsoid.Infeas.lemma_6_2_a
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T08:39:48.761136+00:00
-- url     : https://prove2.me/theorems/7790b876-932a-4402-ac22-feb61163d722
-- title:
--   Lemma 6.2(a) — the updated lower bound satisfies $\ell^{(2)}_j\le\max\{\ell_j,L_j\}$
-- statement:
--   Let $A$ satisfy Assumption 1.1, let $d>0$, and let $\ell$ be a certified lower bound for $(P)$ with certificate matrix $\Lambda$, normalized so that $f(d,\ell)=1$. Let $j\in[m]$ satisfy
--
--   $$0<a_j^\top y(d,\ell)-u_j\le\gamma_j(d,\ell),$$
--
--   and put $L_j:=a_j^\top y(d,\ell)-\gamma_j(d,\ell)$. Define $\ell^{(1)}=\ell-\frac{2(t_j(d,\ell)-v_j(\ell))}{d_j\gamma_j(d,\ell)^2}e_j$ as in (18) and suppose $f(d,\ell^{(1)})>0$; then define $d^{(1)}=d/f(d,\ell^{(1)})$ as in (21) and
--
--   $$\ell^{(2)}=\ell^{(1)}+\frac{2\big(2v_j(\ell^{(1)})-\gamma_j(d^{(1)},\ell^{(1)})\big)}{(m-1)d^{(1)}_j\gamma_j(d^{(1)},\ell^{(1)})^2+2}\,e_j$$
--
--   as in (22). Then
--
--   $$\ell^{(2)}_j\le\max\{\ell_j,L_j\}.$$
--
--   Since $\ell^{(2)}$ agrees with $\ell$ off coordinate $j$, this is what makes $\ell^{(2)}$ a certified lower bound once column $j$ of the certificate matrix certifies $\max\{\ell_j,L_j\}$ (Steps 5-8 of Algorithm 4); it is the invariant that keeps the oblivious ellipsoid algorithm's lower bounds certified from one iteration to the next.
--
--   **Formalization Note** The formal statement records the inequality of item (a); the consequence "hence $\ell^{(2)}$ is certified" is the column-replacement bookkeeping of Algorithm 4. The updates are the platform definitions `ell1`, `d1`, `ell2`, and $L_j$ is `Lb`.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 18, Lemma 6.2(a) (updates (18), (21), (22); proof on p. 43)

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Lemma 6.2(a), p. 18. -/
theorem lemma_6_2_a {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (Lam : Matrix (Fin m) (Fin m) ℝ)
    (hA : Assumption11 A) (hd : ∀ i, 0 < d i)
    (hcert : CertLB A u ell Lam) (hf : f A u d ell = 1) (j : Fin m)
    (hviol : 0 < col A j ⬝ᵥ y A u d ell - u j)
    (hle : col A j ⬝ᵥ y A u d ell - u j ≤ slabRadius A u d ell j)
    (hf1 : 0 < f A u d (ell1 A u d ell j)) :
    ell2 A u d ell j j ≤ max (ell j) (Lb A u d ell j) := by sorry

end OblivEllipsoid.Infeas
