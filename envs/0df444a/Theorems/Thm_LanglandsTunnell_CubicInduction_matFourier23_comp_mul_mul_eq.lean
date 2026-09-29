-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_mul_eq
-- name    : LanglandsTunnell.CubicInduction.matFourier23_comp_mul_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b2e95ea8-ca75-5101-8b00-e84e680cb9b9
-- title:
--   Fourier transform on M_{2× 3} under left and right translation
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_v$ for the $v$-adic completion, and let $\eta$ be a complex additive character of $F$. Let $n$ be an integer and assume that $\eta(x) = 1$ for every $x$ with $\mathrm{v}(x) \le \exp(n)$, while some $x$ with $\mathrm{v}(x) \le \exp(n+1)$ has $\eta(x) \neq 1$; thus $\eta$ is trivial on one valuation ball and nontrivial on the next, fixing its level. Let $\varphi : M_{2\times 3}(F) \to \mathbb{C}$ be Schwartz–Bruhat, i.e. locally constant with compact support, let $h \in \mathrm{GL}_2(F)$, $g \in \mathrm{GL}_3(F)$, and let $X \in M_{2\times 3}(F)$. Denote by $\mathcal{F}_\eta =$ `matFourier23 v η` the threefold iterated column transform `colFourier23` in columns $0$, $1$, $2$, where the $j$-th such transform sends $\Phi$ to $X \mapsto \int_{F\times F} \Phi(\mathtt{setCol23}\ v\ X\ j\ u)\,\eta(u_1 X_{0j} + u_2 X_{1j})$ against the square of the self-dual Haar measure at $v$. Then $$\mathcal{F}_\eta\bigl(Y \mapsto \varphi(hYg)\bigr)(X) = \mathrm{mod}(\det h)^{-3}\,\mathrm{mod}(\det g)^{-2}\; \mathcal{F}_\eta\varphi\bigl({}^t h^{-1}\, X\, {}^t g^{-1}\bigr),$$ where $\mathrm{mod}$ is the module of multiplication on $F$ (the `distribHaarChar` scaling factor, equal to the $v$-adic norm) and ${}^t(\cdot)^{-1}$ is `transposeInvN`, the transpose of the inverse in the relevant general linear group.
--
--   This is the standard equivariance of the Fourier transform on the space of $2 \times 3$ matrices over a local field under the left $\mathrm{GL}_2$ and right $\mathrm{GL}_3$ translation actions, with the Jacobian factors $|\det h|^{-3}|\det g|^{-2}$ and the contragredient action on the dual variable. It is used in the local Godement–Jacquet theory of the Rankin–Selberg integral for $\mathrm{GL}_2 \times \mathrm{GL}_3$, where it feeds the functional equation relating the Godement section of a Whittaker function to that of its dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_mul_eq.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.matFourier23_comp_mul_mul_eq
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hφ : IsSchwartzBruhat φ)
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (g : GL (Fin 3) (v.adicCompletion ℚ))
    (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    matFourier23 v η (fun Y => φ ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y *
        (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) X =
      ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ ^ 3 *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ ^ 2 *
        matFourier23 v η φ
          ((transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * X *
            (transposeInvN (Fin 3) g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by sorry
