-- Prove2me | Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
-- name    : MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/e57a6590-ca6b-5247-baf1-3d180a5734cb
-- title:
--   Maximal growth persists under a general hyperplane section
-- statement:
--   Fix natural numbers $n$ and $m$ and an infinite field $K$, and put $S = K[x_0,\dots,x_n]$ (the polynomial ring `MvPolynomial (Fin (n + 1)) K`). For an ideal $I$ of $S$ and a degree $d$, write $(S/I)_d$ for the quotient of the space of forms of degree $d$ by the forms of degree $d$ lying in $I$ (the project's `piece I d`), and let $a \mapsto a^{\langle d\rangle}$ denote Macaulay's pseudo-power [`Nat.macaulayPow d`](def/Nat_MacaulayPow.html#L7). Let $J \subseteq S$ be an ideal admitting a generating set consisting of forms of degree $m$, i.e. $J = \operatorname{span}(s)$ for some set $s$ all of whose elements are homogeneous of degree $m$, and assume maximal growth from $m$ to $m+1$: $\dim_K (S/J)_{m+1} = \bigl(\dim_K (S/J)_m\bigr)^{\langle m\rangle}$. The assertion is that there exists a nonzero $G \in S$ such that for every $a : \mathrm{Fin}(n+1) \to K$ with $G(a) \ne 0$, setting $\ell_a = \sum_i a_i x_i$, the following three statements hold: (i) every form $f$ of degree $m$ with $\ell_a f \in J$ already lies in $J$, i.e. $(J : \ell_a)_m = J_m$; (ii) $J \vee (\ell_a)$ again has maximal growth, $\dim_K (S/(J + (\ell_a)))_{m+1} = \bigl(\dim_K (S/(J + (\ell_a)))_m\bigr)^{\langle m\rangle}$; and (iii) $\bigl(\dim_K (S/(J + (\ell_a)))_m\bigr)^{\langle m\rangle} + \dim_K (S/J)_m = \bigl(\dim_K (S/J)_m\bigr)^{\langle m\rangle}$, so that Green's hyperplane restriction bound is attained.
--
--   This is the equality case of Green's hyperplane restriction theorem for an ideal generated in degree $m$ whose Hilbert function grows maximally from degree $m$ to degree $m+1$; it is the numerical step underlying Gotzmann's persistence theorem. It is cited in the construction of a general linear form with maximal growth on projective space and in the variant of the present statement for an ideal that is not assumed generated in degree $m$; the proof invokes Macaulay's bound [`MvPolynomial.finrank_piece_succ_le_macaulayPow`](thm.html#MvPolynomial.finrank_piece_succ_le_macaulayPow) and Green's inequality [`MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le`](thm.html#MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      (∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m → (∑ i, C (a i) * X i) * f ∈ J → f ∈ J) ∧
      Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) (m + 1)) =
        Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) ∧
      Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) +
          Module.finrank K (piece J m) = Nat.macaulayPow m (Module.finrank K (piece J m)) := by sorry
