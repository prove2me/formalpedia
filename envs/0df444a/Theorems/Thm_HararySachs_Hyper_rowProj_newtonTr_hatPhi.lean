-- Prove2me | Theorems.Thm_HararySachs_Hyper_rowProj_newtonTr_hatPhi
-- name    : HararySachs.Hyper.rowProj_newtonTr_hatPhi
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T03:02:05.537454+00:00
-- url     : https://prove2.me/theorems/113d461c-e111-4e1d-9f31-44feaa17f983
-- title:
--   Row invariance of the Poisson numerators $S_m$
-- statement:
--   Let $n \ge 1$, $k \ge 2$, $r = k-1$, and let $\operatorname{Res}$ be the normalized resultant of $n$ forms of degree $r$. For the generic tensor $\mathbb{A}$, let
--   $$Q = \operatorname{Res}\bigl(x^{[r]} - \mathbb{A}x^{r}\bigr)$$
--   be the full resultant (all $X_{j,t}$ free). Fix a row $i$, and split $Q$ by its degree in the row-$i$ variables: $Q = \sum_j q_j$ with $C = q_0$. Let $S_m$ be the $m$-th Newton trace of $1 + \sum_{j=1}^{m} C^{\,j-1} q_j s^j$; in other words $S_m = C^m\sigma_m$, where $-\sigma_m/m$ is the row-degree-$m$ part of $\log Q$. Then
--   $$\Pi_{i,m}(S_m) = S_m,$$
--   where $\Pi_{i,m}$ is the row projection of the definition `rowProj`.
--
--   At a generic numeric point, Poisson's formula gives $S_m = C^m\sum_p f_i(p)^m$. Here $p$ runs over the common zeros, normalized by $p_i = 1$, of the other $n-1$ equations. The shift operator recovers $f_i(p)^m$ from $(v\cdot p)^{rm}$, and density extends the identity to all coefficients. This is the step where the degree-preserving variant replaces the linear equation of Morozov–Shakirov.
--
--   **Formalization Note** $Q$ is `(phiPoly (genTensor n k) res).eval 1`. The pieces $q_j$ are `weightedHomogeneousComponent (rowWeight i) j Q`, and $\widehat\Phi$ is `hatPhi`.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 3, proof of Proposition I (Poisson product formula and shift operator (15)), in the variant of mission strategy comments 2173f2a9-fd2e-4d5e-afb5-27607d970161 and 8357894d-0c47-45af-94e5-d71263b245a7.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Definitions.Def_HararySachs_Hyper_RowProj

namespace HararySachs.Hyper

theorem rowProj_newtonTr_hatPhi (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res) (i : Fin n) (m : ℕ) :
    rowProj i m (newtonTr (hatPhi
        (MvPolynomial.weightedHomogeneousComponent (rowWeight i) 0
          ((phiPoly (k := k) (genTensor n k) res).eval 1))
        (fun j => MvPolynomial.weightedHomogeneousComponent (rowWeight i) j
          ((phiPoly (k := k) (genTensor n k) res).eval 1)) m) m) =
      newtonTr (hatPhi
        (MvPolynomial.weightedHomogeneousComponent (rowWeight i) 0
          ((phiPoly (k := k) (genTensor n k) res).eval 1))
        (fun j => MvPolynomial.weightedHomogeneousComponent (rowWeight i) j
          ((phiPoly (k := k) (genTensor n k) res).eval 1)) m) m := by sorry

end HararySachs.Hyper
