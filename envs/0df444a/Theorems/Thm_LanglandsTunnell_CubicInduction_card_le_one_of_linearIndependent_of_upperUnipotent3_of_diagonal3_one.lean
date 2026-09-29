-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
-- name    : LanglandsTunnell.CubicInduction.card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/2861babb-3369-53b4-81a5-f5aef15ad537
-- title:
--   At most one such functional on the trivial principal series of GL₃
-- statement:
--   Let $v$ be a height-one prime of $\mathcal O_{\mathbb Q}$, with completion $\mathbb Q_v$, and let $P = \mathrm{principalSeries3}\,v\,(\lambda i.\,1)$ be the $\mathbb C$-subspace of functions $f : GL_3(\mathbb Q_v) \to \mathbb C$ that are locally constant, satisfy $f(u g) = f(g)$ for every upper unipotent $u = \begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$ with $x,y,z \in \mathbb Q_v$, and satisfy $f(\mathrm{diag}(a_0,a_1,a_2)\,g) = \big(\prod_i 1(a_i)\big)\cdot(\lVert a_0\rVert/\lVert a_2\rVert)\cdot f(g)$ for all $a \in (\mathbb Q_v^\times)^3$, the character triple being trivial so that the first factor is $1$. Let $s$ be a finite set of $\mathbb C$-linear functionals $\Lambda : P \to \mathbb C$. Assume: (i) each $\Lambda \in s$ is invariant under right translation by upper unipotent matrices, i.e. $\Lambda(g \mapsto f(g u)) = \Lambda(f)$ for all $x,y,z$ and all $f \in P$; (ii) each $\Lambda \in s$ satisfies $\Lambda(g \mapsto f(g\,\mathrm{diag}(a))) = \big(\prod_i 1(a_i)\big)(\lVert a_0\rVert/\lVert a_2\rVert)\,\Lambda(f)$ for all $a \in (\mathbb Q_v^\times)^3$ and $f \in P$; (iii) the family of elements of $s$, viewed inside $P \to_{\mathbb C} \mathbb C$, is $\mathbb C$-linearly independent. Then $s$ has at most one element.
--
--   This is a multiplicity bound of geometric-lemma type for the $GL_3$ principal series attached to the trivial character triple: functionals transforming under the diagonal torus by exactly the half-modulus factor $\lVert a_0\rVert/\lVert a_2\rVert$ and invariant under right unipotent translation span a space of dimension at most one, rather than one of dimension equal to the number of Weyl elements fixing a general triple. It is used in [`LanglandsTunnell.CubicInduction.exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq`](thm.html#LanglandsTunnell.CubicInduction.exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq), where an operator commuting with right translation is pinned down as a scalar multiple of the identity, and it rests on the smoothness statement that every element of the principal series is fixed by right translation by a sufficiently small congruence neighbourhood of the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
    (v : HeightOneSpectrum (𝓞 ℚ))
    (s : Finset (↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)) :
    (∀ Λ ∈ s, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f) →
    (∀ Λ ∈ s, ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f) →
    (LinearIndependent ℂ (fun Λ : ↥s => (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ))) →
    s.card ≤ 1 := by sorry
