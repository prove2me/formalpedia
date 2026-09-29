-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
-- name    : LanglandsTunnell.CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/e45bb2ae-6c73-514f-8ab5-fd52d1ebee4c
-- title:
--   Principal series vectors of p-adic GL₃ are smooth
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, let $\chi = (\chi_0,\chi_1,\chi_2)$ be a triple of multiplicative characters $(\mathbb{Q}_v)^\times \to \mathbb{C}^\times$ of the units of the $v$-adic completion of $\mathbb{Q}$, and let $f : GL_3(\mathbb{Q}_v) \to \mathbb{C}$ belong to the $\mathbb{C}$-submodule `principalSeries3 v χ`, that is: $f$ is locally constant; $f(u g) = f(g)$ for every upper unipotent $u = \begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$ with $x,y,z \in \mathbb{Q}_v$ and every $g$; and $f(\mathrm{diag}(a_0,a_1,a_2)\,g) = \big(\prod_{i}\chi_i(a_i)\big)\cdot \big(\lVert a_0\rVert/\lVert a_2\rVert\big)\cdot f(g)$ for all units $a_i$ and all $g$, the second factor being the real ratio of absolute values viewed in $\mathbb{C}$. The conclusion is that there exists $n \in \mathbb{N}$ such that every $k \in GL_3(\mathbb{Q}_v)$ whose entries satisfy $v(k_{ij} - \delta_{ij}) \le \exp(-n)$ for all $i,j$ fixes $f$ under right translation: the endomorphism `gl3AmbientRightTranslate` sending a function $W$ to $h \mapsto W(hk)$ carries $f$ to $f$ itself. Thus $f$ is invariant under the level-$n$ principal congruence subgroup, with $n$ allowed to depend on $f$.
--
--   This is the smoothness of vectors in the principal series of $GL_3$ over a $p$-adic field: each such function is fixed by an open compact subgroup, here taken in the explicit form of a principal congruence subgroup. It underlies the later analysis of the induced representation in the cubic-induction construction, for instance the results on linear independence of translates and on the existence of invariant complements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : LocalGL3 v → ℂ) (hf : f ∈ principalSeries3 v χ) :
    ∃ n : ℕ, ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k f = f := by sorry
