-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3
-- name    : LanglandsTunnell.CubicInduction.mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/3860bd24-63be-57d6-9f72-c3e5c53a0bef
-- title:
--   Vanishing along the (2,1) radical of a θ-isotypic principal series vector
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_v$ for the $v$-adic completion, and let $\chi_0,\chi_1,\chi_2$ be homomorphisms $\mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$. Let $F:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ lie in `principalSeries3`, i.e. $F$ is locally constant, satisfies $F(n(x,y,z)g)=F(g)$ for every upper unitriangular $n(x,y,z)$ (entries $x,y,z$ in positions $(1,2)$, $(2,3)$, $(1,3)$) and every $g$, and satisfies $F(\mathrm{diag}(a_0,a_1,a_2)g)=\bigl(\prod_i\chi_i(a_i)\bigr)\,(\lVert a_0\rVert/\lVert a_2\rVert)\,F(g)$ for all units $a_i$ and all $g$. Assume $F$ is smooth in the sense that some open subgroup $U\le\mathrm{GL}_3(\mathbb{Q}_v)$ satisfies $F(gk)=F(g)$ for all $k\in U$, $g\in\mathrm{GL}_3(\mathbb{Q}_v)$. Let $\theta:\mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$ be a homomorphism such that $F(g\,\mathrm{diag}(1,1,u))=\theta(u)F(g)$ for all $g$ and all units $u$ of valuation $1$, and assume that for each $i\in\{0,1,2\}$ there is a unit $u$ of valuation $1$ with $\theta(u)\neq\chi_i(u)$. Then $F$ belongs to the $\mathbb{C}$-span of the functions $g\mapsto G(g\,n(0,w_1,w_0))-G(g)$, where $w\in\mathbb{Q}_v^{2}$ and $G$ ranges over `principalSeries3` for the same $\chi$.
--
--   The conclusion is the statement that the image of $F$ in the Jacquet module of the normalised principal series $I(\chi_0,\chi_1,\chi_2)$ of $\mathrm{GL}_3(\mathbb{Q}_v)$ along the unipotent radical $\{n(0,y,z)\}$ of the standard parabolic of type $(2,1)$ vanishes, under the assumption that the compact torus $\mathrm{diag}(1,1,\mathcal{O}_v^{\times})$ acts on $F$ through a character $\theta$ differing from each $\chi_i$ on units. It is obtained from the companion statement for the parabolic of type $(1,2)$, with $\mathrm{diag}(u,1,1)$ and the radical $\{n(x,0,z)\}$, and is used in the construction of vanishing type integrals in [`LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_fst`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_fst).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (F : LocalGL3 v → ℂ) (hF : F ∈ principalSeries3 v χ)
    (hsm : ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ k ∈ U, ∀ g : LocalGL3 v, F (g * k) = F g)
    (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hθ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      ∀ g : LocalGL3 v, F (g * diagonal3 v ![1, 1, u]) = ((θ u : ℂˣ) : ℂ) * F g)
    (hne : ∀ i : Fin 3, ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧ θ u ≠ χ i u) :
    F ∈ Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
      G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP21 w) G - G} := by sorry
