-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen
-- name    : LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/449222a1-5a7e-559a-8c0b-c345bba6efc0
-- title:
--   Bump function on GL₂ from translates of a GL₃ Whittaker function
-- statement:
--   Let $v$ be a height one prime of $\mathcal{O}_{\mathbb{Q}}$ and write $\mathbb{Q}_v$ for the completion of $\mathbb{Q}$ at $v$. Let $\psi$ be a non-trivial additive character of $\mathbb{Q}_v$ with values in $\mathbb{C}$, and let $W : GL_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy `IsGL3PsiWhittakerFn`, i.e. $W(n(x,y,z)g) = \psi(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and all $g$, where $n(x,y,z)$ is the upper unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the corner; assume further that $W$ is right invariant under some open subgroup of $GL_3(\mathbb{Q}_v)$, and that $W \neq 0$. Let $t_0 \in GL_2(\mathbb{Q}_v)$ and let $U_1$ be a subgroup of $GL_2(\mathbb{Q}_v)$ that is compact and open as a subset, such that $\psi(x) = 1$ whenever $t_0^{-1} n(x) t_0 \in U_1$, with $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$. Then there is a $W'$ in the $\mathbb{C}$-span of the right translates $h \mapsto W(hg)$ of $W$ ($g \in GL_3(\mathbb{Q}_v)$) such that, writing $\iota(h) = \mathrm{diag}(h,1) \in GL_3(\mathbb{Q}_v)$ for $h \in GL_2(\mathbb{Q}_v)$: $W'(\iota(hk)) = W'(\iota(h))$ for all $k \in U_1$ and all $h$; whenever $W'(\iota(h)) \neq 0$ one has $h = n(x) t_0 k$ for some $x \in \mathbb{Q}_v$ and some $k \in U_1$; and $W'(\iota(t_0)) = 1$.
--
--   This is the construction of a normalised "bump" vector at the place $v$: a finite linear combination of right translates of a local $GL_3$ Whittaker function whose restriction along the standard embedding $GL_2 \hookrightarrow GL_3$ is right $U_1$-invariant, supported in the single cell $N_2(\mathbb{Q}_v) t_0 U_1$, and equal to $1$ at $t_0$, for an arbitrary prescribed compact open $U_1$ compatible with $\psi$ in the stated sense. It refines [`LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump`](thm.html#LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump), where the invariance subgroup is produced by the statement rather than prescribed, and is used in the Rankin–Selberg computations that isolate a single local integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_iotaGL_bump_of_isCompact_of_isOpen
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψ : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hne : W ≠ 0) (t₀ : GL (Fin 2) (v.adicCompletion ℚ)) (U₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hU₁ : IsCompact (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hU₁' : IsOpen (U₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hψU₁ : ∀ x : v.adicCompletion ℚ, t₀⁻¹ * unipotentGL2 x * t₀ ∈ U₁ → ψ x = 1) :
    ∃ W' ∈ gl3CyclicSubspace W,
      (∀ k ∈ U₁, ∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL (h * k)) = W' (iotaGL h)) ∧
      (∀ h : GL (Fin 2) (v.adicCompletion ℚ), W' (iotaGL h) ≠ 0 →
        ∃ x : v.adicCompletion ℚ, ∃ k ∈ U₁, h = unipotentGL2 x * t₀ * k) ∧
      W' (iotaGL t₀) = 1 := by sorry
