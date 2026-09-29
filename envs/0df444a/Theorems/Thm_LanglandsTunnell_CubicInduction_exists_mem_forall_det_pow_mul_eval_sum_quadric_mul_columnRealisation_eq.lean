-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq
-- name    : LanglandsTunnell.CubicInduction.exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/1d1a4f6a-4147-5c00-9df2-4d812cee6280
-- title:
--   Quadric read-outs of a twisted column realisation stay in V
-- statement:
--   Let $V$ be a $\mathbb C$-submodule of the complex-valued functions on $\mathrm{GL}_3$ of the adeles of $\mathbb Q$, and let $k_1$ be an adelic matrix whose archimedean component is $1$. Assume: every $G\in V$ is archimedean-smooth, i.e. for each $g$ the map $e\mapsto G(g\cdot \mathtt{archRealLift3}\,e)$ is $C^\infty$ on the real $3\times 3$ matrices of nonzero determinant, where $\mathtt{archRealLift3}\,e$ is the adelic unit given by $e$ at the infinite place (and $1$ if that matrix fails to be invertible); $V$ is stable under right translation by any $k'$ which is $1$ at every height-one prime and whose archimedean component $k'_\infty$ satisfies $k'^{\mathsf T}_\infty k'_\infty=1$; and for each $G\in V$ and each pair of indices $(c_0,d_0)$ there is $G'\in V$ with $G'(g)$ the derivative at $s=0$ of $s\mapsto G(g\cdot \mathtt{archRealLift3}(1+sE_{c_0d_0}))$. Let $\ell\in\mathbb N$, let $p\in\mathbb C[X_0,X_1,X_2]$ be homogeneous of degree $\ell$, fix a column index $j$ and $\alpha\in\mathbb N$, and let $G\in V$ satisfy, for every real $o$ with orthonormal columns ($\sum_a o_{ai}o_{aj'}=\delta_{ij'}$), $\det(o)^\alpha\,p(o_{0j},o_{1j},o_{2j})=G(\mathtt{archRealLift3}\,o\cdot k_1)$; here and below substitution of $X_a\mapsto X_{(a,j)}$ means reading the $j$-th column. The conclusion is the conjunction of three statements, each asserting that for all indices $a,b$ there is $G'\in V$ with, for every real $o$ with orthonormal columns, $G'(\mathtt{archRealLift3}\,o\cdot k_1)$ equal to the value at the entries of $o$ of, respectively, $\det(o)^{\alpha}\sum_{i,i'}o_{ia}o_{i'b}(\partial_i\partial_{i'}p)(o_{\cdot j})$; $\det(o)^{\alpha+1}\sum_{i,i'}\tfrac12(o_{ia}o_{i'b}+o_{ib}o_{i'a})\bigl(\sum_{c,d}\tfrac{(i'-c)(c-d)(d-i')}{2}X_c\,\partial_d\partial_i p\bigr)(o_{\cdot j})$, the coefficient being formed from the indices regarded as the naturals $0,1,2$ in $\mathbb C$; and $\det(o)^{\alpha}\sum_{i,i'}\tfrac12(o_{ia}o_{i'b}+o_{ib}o_{i'a})\bigl(X_{i'}\partial_i p-\tfrac13(\sum_e X_e^2)\,\partial_i\partial_{i'}p\bigr)(o_{\cdot j})$.
--
--   The three expressions are the quadric twists of a degree-$\ell$ column read-out by the second-order operator $\partial_a\partial_b$, by the symmetrised rotation generator $\sum_{c,d}\varepsilon_{acd}x_c\partial_d$ (whose pseudo-vector nature accounts for the extra factor of $\det$), and by the trace-free part of $x_b\partial_a$; the statement says that each is again read off by a member of $V$. It supplies the archimedean input to the transition identities used by [`LanglandsTunnell.CubicInduction.exists_read_lowerOne_xi_of_read_signIsotypic`](thm.html#LanglandsTunnell.CubicInduction.exists_read_lowerOne_xi_of_read_signIsotypic), `…exists_read_lowerTwo_xi_of_read_signIsotypic` and `…exists_read_sameTwo_xi_of_read_signIsotypic`, and its proof cites the spanning of the dual of the homogeneous polynomials of degree $\ell$ by point evaluations on the sphere ([`LanglandsTunnell.CubicInduction.exists_sum_mul_eval_sphere_eq_of_isHomogeneous`](thm.html#LanglandsTunnell.CubicInduction.exists_sum_mul_eval_sphere_eq_of_isHomogeneous)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_mem_forall_det_pow_mul_eval_sum_quadric_mul_columnRealisation_eq
    (V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hsm : ∀ G ∈ V, WhittakerBlock.IsArchSmooth3 G)
    (hstab : ∀ G ∈ V, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ q : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ q k' = 1) →
      archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ V)
    (hflow : ∀ G ∈ V, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ) (j : Fin 3) (α : ℕ)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ V)
    (hreal : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ α *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (p)) = G (WhittakerBlock.archRealLift3 o * k₁)) :
    (∀ a b : Fin 3, ∃ G' ∈ V, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ α *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.X (i, a) * MvPolynomial.X (i', b) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) =
      G' (WhittakerBlock.archRealLift3 o * k₁)) ∧
    (∀ a b : Fin 3, ∃ G' ∈ V, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (α + 1) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.C (1 / 2 : ℂ) *
            (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (∑ c : Fin 3, ∑ d : Fin 3,
              MvPolynomial.C ((((i' : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
                (((d : ℕ) : ℂ) - ((i' : ℕ) : ℂ)) / 2) *
                (MvPolynomial.X c * MvPolynomial.pderiv d (MvPolynomial.pderiv i p)))) =
      G' (WhittakerBlock.archRealLift3 o * k₁)) ∧
    (∀ a b : Fin 3, ∃ G' ∈ V, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ α *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (∑ i : Fin 3, ∑ i' : Fin 3, MvPolynomial.C (1 / 2 : ℂ) *
            (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
            MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (MvPolynomial.X i' * MvPolynomial.pderiv i p -
              MvPolynomial.C (1 / 3 : ℂ) * (∑ e : Fin 3, MvPolynomial.X e ^ 2) *
                MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) =
      G' (WhittakerBlock.archRealLift3 o * k₁)) := by sorry
