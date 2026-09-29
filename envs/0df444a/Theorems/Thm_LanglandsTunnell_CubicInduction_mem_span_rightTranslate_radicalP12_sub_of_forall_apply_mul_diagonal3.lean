-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3
-- name    : LanglandsTunnell.CubicInduction.mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f5981dd7-0e46-5526-b0ba-7f5220fc37af
-- title:
--   Vanishing of a θ-isotypic vector in a (1,2) Jacquet module
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_v$ for the $v$-adic completion, and let $\chi : \mathrm{Fin}\,3 \to \mathrm{Hom}(\mathbb{Q}_v^\times, \mathbb{C}^\times)$ be a triple of multiplicative characters. Let $F : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ belong to `principalSeries3 v χ`, that is: $F$ is locally constant, $F(n g) = F(g)$ for every upper unitriangular $n =$ `upperUnipotent3 x y z` with entries $x, y, z$ in positions $(1,2), (2,3), (1,3)$, and $F(\mathrm{diag}(a_0,a_1,a_2)\,g) = \bigl(\prod_i \chi_i(a_i)\bigr)\,(\lVert a_0\rVert/\lVert a_2\rVert)\,F(g)$ for all units $a_i$ and all $g$. Assume in addition that $F$ is right invariant under some open subgroup $U \le \mathrm{GL}_3(\mathbb{Q}_v)$, i.e. $F(gk) = F(g)$ for all $k \in U$ and all $g$. Let $\theta$ be a further character of $\mathbb{Q}_v^\times$ such that $F(g\,\mathrm{diag}(u,1,1)) = \theta(u) F(g)$ for all $g$ and all units $u$ of valuation $1$, and assume that for each $i \in \{0,1,2\}$ there is a unit $u$ of valuation $1$ with $\theta(u) \neq \chi_i(u)$. Then $F$ lies in the $\mathbb{C}$-linear span of the set of functions of the form $g \mapsto G(g\,n) - G(g)$, where $G$ ranges over `principalSeries3 v χ` and $n =$ `radicalP12 w` $=$ `upperUnipotent3 (w 0) 0 (w 1)` ranges over the unipotent radical of the standard parabolic of type $(1,2)$, parametrised by $w : \mathrm{Fin}\,2 \to \mathbb{Q}_v$.
--
--   This is the statement that the $\theta$-isotypic vectors for the compact torus $\{\mathrm{diag}(u,1,1)\}$ die in the Jacquet module of the normalised principal series $I(\chi_0,\chi_1,\chi_2)$ of $\mathrm{GL}_3(\mathbb{Q}_v)$ along the unipotent radical of the type $(1,2)$ parabolic, under the assumption that $\theta$ differs from each inducing character $\chi_i$ on the units; membership in the span of differences $R(n)G - G$ is the concrete form of vanishing in that Jacquet module. It is used in the cubic induction package, both for the companion statement along the type $(2,1)$ radical and for the vanishing of the associated type integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (F : LocalGL3 v → ℂ) (hF : F ∈ principalSeries3 v χ)
    (hsm : ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ k ∈ U, ∀ g : LocalGL3 v, F (g * k) = F g)
    (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hθ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      ∀ g : LocalGL3 v, F (g * diagonal3 v ![u, 1, 1]) = ((θ u : ℂˣ) : ℂ) * F g)
    (hne : ∀ i : Fin 3, ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧ θ u ≠ χ i u) :
    F ∈ Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
      G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP12 w) G - G} := by sorry
