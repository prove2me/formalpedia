-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/cfa60530-f48d-5a89-8d01-dd5e3b380ebc
-- title:
--   Whittaker-type function on GL₂(ℚᵥ) with prescribed torus values
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and let $\chi$ be a complex-valued additive character of the completion $\mathbb{Q}_v$ which is trivial on every element of valuation at most $1$. Let $\varpi$ be an element of the valuation ring of $\mathbb{Q}_v$ whose image $\pi$ in $\mathbb{Q}_v$ is non-zero and satisfies $\mathrm{v}(\pi) = \exp(-1)$, let $z$ be a non-zero complex number, and let $N$, $\mathrm{lam}$, $\mathrm{om}$ be arbitrary complex numbers. Then there exists a function $W_2 : GL_2(\mathbb{Q}_v) \to \mathbb{C}$ with the following five properties: (1) $W_2(n(x)g) = \chi(x) W_2(g)$ for all $x \in \mathbb{Q}_v$ and all $g$, where $n(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$; (2) $W_2(gk) = W_2(g)$ for all $g$ and all $k$ in the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), that is, the preimage under the local embedding $GL_2(\mathbb{Q}_v) \to GL_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the finite-adelic level-one subgroup attached to the unit ideal $\top$, whose members are the $g$ for which both $g$ and $g^{-1}$ satisfy `IsLevelOneMatrix` for $\top$; (3) $W_2(1) = 1$; (4) $W_2\big(g \cdot \mathrm{diag}(\pi,\pi)\big) = z\, W_2(g)$ for all $g$; (5) for every integer $m$, $W_2\big(\mathrm{diag}(\pi^m, 1)\big)$ equals $\mathrm{torusFactor}\,N\,\mathrm{lam}\,\mathrm{om}\,m$, which is $0$ for $m < 0$ and for $m \geq 0$ is the $m$-th term $u_m$ of the recursion $u_0 = 1$, $u_1 = \mathrm{lam}/N$, $u_{m+2} = (\mathrm{lam}\,u_{m+1} - \mathrm{om}\,u_m)/N$.
--
--   This is the local existence statement for an unramified Whittaker-type function at a finite place: a function on $GL_2(\mathbb{Q}_v)$ transforming by $\chi$ on the upper unipotent subgroup, right invariant under the level-one group at the unit ideal, with prescribed central scaling factor $z$ and prescribed values along the torus elements $\mathrm{diag}(\pi^m,1)$ given by the three-term Hecke recursion. It is used by the cubic-induction lemmas producing normalised new vectors and by the computation of spherical torus values of induced coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.exists_unipotent_localLevelOne_scalarPi_diagZ_torusFactor_of_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : AddChar (v.adicCompletion ℚ) ℂ)
    (hχ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → χ x = 1)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (z : ℂ) (hz : z ≠ 0) (N lam om : ℂ) :
    ∃ W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ,
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = χ x * W₂ g) ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g) ∧
      W₂ 1 = 1 ∧
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = z * W₂ g) ∧
      ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
        torusFactor N lam om m := by sorry
