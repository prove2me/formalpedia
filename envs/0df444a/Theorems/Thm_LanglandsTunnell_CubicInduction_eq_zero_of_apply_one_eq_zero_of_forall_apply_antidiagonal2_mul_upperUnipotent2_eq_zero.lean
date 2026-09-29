-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_zero
-- name    : LanglandsTunnell.CubicInduction.eq_zero_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/32734423-8058-5530-bb09-6e691ac311bc
-- title:
--   Principal-series vectors vanishing at 1 and on the big cell
-- statement:
--   Fix a height-one prime $p$ of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ and a pair $\theta = (\theta_0,\theta_1)$ of monoid homomorphisms from the units of the $p$-adic completion $F = \mathbb{Q}_p$ of $\mathbb{Q}$ at $p$ to $\mathbb{C}^\times$. Let $f$ be an element of the $\mathbb{C}$-submodule `principalSeries2 p θ` of functions $G = \mathrm{GL}_2(F) \to \mathbb{C}$, that is, $f$ is locally constant, satisfies $f(n(x)g) = f(g)$ for all $x \in F$ and $g \in G$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $f(\mathrm{diag}(a_0,a_1)\,g) = \theta_0(a_0)\theta_1(a_1)\,\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\; f(g)$ for all $a_0,a_1 \in F^\times$ and $g \in G$. Assume that $f(1) = 0$ and that $f(w\,n(x)) = 0$ for every $x \in F$, where $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ (the element `antidiagonal2 p`, an invertible matrix by its nonzero determinant). Then $f$ is the zero element of the submodule.
--
--   This is the statement that a vector in the normalised principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$ is determined by its value at the identity together with its profile $x \mapsto f(w\,n(x))$ on the big Bruhat cell, a consequence of the decomposition $G = B \sqcup B w N$. It is used in the proof of the vanishing of determinant-equivariant functionals on a unitary principal series, [`LanglandsTunnell.CubicInduction.eq_zero_of_forall_apply_principalSeries2Rep_eq_det_mul_of_norm_eq_one`](thm.html#LanglandsTunnell.CubicInduction.eq_zero_of_forall_apply_principalSeries2Rep_eq_det_mul_of_norm_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zero_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.eq_zero_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_zero
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries2 p θ))
    (h1 : (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) 1 = 0)
    (hw : ∀ x : p.adicCompletion ℚ,
      (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (antidiagonal2 p * upperUnipotent2 p x) = 0) :
    f = 0 := by sorry
