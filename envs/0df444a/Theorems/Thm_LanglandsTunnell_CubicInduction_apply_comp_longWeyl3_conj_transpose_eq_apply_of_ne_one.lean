-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one
-- name    : LanglandsTunnell.CubicInduction.apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/9f5ddbd4-cb8d-51e3-b3b8-32f948112e75
-- title:
--   Invariance of bi-Whittaker forms on GL₃ under g↦ w ^tg w
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$ and write $\mathbb{Q}_v$ for the $v$-adic completion of $\mathbb{Q}$, so that `LocalGL3 v` is the group $GL_3(\mathbb{Q}_v)$ of invertible $3\times 3$ matrices over $\mathbb{Q}_v$. Let $\psi_v$ be an additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$, assumed non-trivial, and let $T$ be a $\mathbb{C}$-linear form on the space of all $\mathbb{C}$-valued functions on $GL_3(\mathbb{Q}_v)$ (no continuity or support condition on the domain of $T$). Write $n(x,y,z)$, for $x,y,z\in\mathbb{Q}_v$, for the unit of $GL_3(\mathbb{Q}_v)$ with underlying matrix $!![1,x,z;0,1,y;0,0,1]$ (the predicate `upperUnipotent3`), and call $\varphi$ a test function when `IsSchwartzBruhat` holds for it, that is, when $\varphi$ is locally constant and has compact support. Assume two transformation laws for $T$ on test functions: for all $x,y,z$ and every test function $\varphi$, $T\bigl(g\mapsto\varphi(n(x,y,z)^{-1}g)\bigr)=\psi_v(x+y)\,T(\varphi)$, and $T\bigl(g\mapsto\varphi(g\,n(x,y,z))\bigr)=\psi_v(-(x+y))\,T(\varphi)$. Then for every test function $\varphi$ one has $T\bigl(g\mapsto\varphi(w\,(\tau(g))^{-1}w^{-1})\bigr)=T(\varphi)$, where $w$ is `longWeyl3`, the permutation unit with ones on the antidiagonal (equal to its own inverse), and $\tau$ is `transposeInv3`, the map sending $g$ to the unit with underlying matrix $({}^tg^{-1})$; thus $(\tau(g))^{-1}$ has underlying matrix ${}^tg$, and the conclusion reads $T\bigl(g\mapsto\varphi(w\,{}^tg\,w)\bigr)=T(\varphi)$.
--
--   This is the $GL_3$ case of the distribution statement attributed to Gelfand and Kazhdan, here formulated directly for linear forms on locally constant compactly supported functions rather than for distributions: a form transforming on the left and on the right by the character $n(x,y,z)\mapsto\psi_v(x+y)$ of the upper unipotent subgroup is fixed by the order-two anti-automorphism $g\mapsto w\,{}^tg\,w$, which preserves that subgroup and that character. It is the input to `hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace`, where uniqueness of Whittaker functionals for $GL_3(\mathbb{Q}_v)$ is deduced from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.apply_comp_longWeyl3_conj_transpose_eq_apply_of_ne_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (_hψv : ψv ≠ 1)
    (T : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)
    (_hleft : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ ((upperUnipotent3 x y z)⁻¹ * g)) = ψv (x + y) * T φ)
    (_hright : ∀ (x y z : v.adicCompletion ℚ) (φ : LocalGL3 v → ℂ), IsSchwartzBruhat φ →
      T (fun g => φ (g * upperUnipotent3 x y z)) = ψv (-(x + y)) * T φ)
    (φ : LocalGL3 v → ℂ) (_hφ : IsSchwartzBruhat φ) :
    T (fun g => φ (longWeyl3 * (transposeInv3 g)⁻¹ * longWeyl3⁻¹)) = T φ := by sorry
