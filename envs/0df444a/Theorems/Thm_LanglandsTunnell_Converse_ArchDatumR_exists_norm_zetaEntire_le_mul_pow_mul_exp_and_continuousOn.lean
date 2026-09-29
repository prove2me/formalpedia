-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn
-- name    : LanglandsTunnell.Converse.ArchDatumR.exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/c316024c-b8ad-5157-95d5-d34500ccff72
-- title:
--   Uniform strip bounds and continuity in g of the entire zeta function
-- statement:
--   Let $P$ be a real archimedean parameter (either a principal datum given by exponents $u_1,u_2\in\mathbb{C}$ and parities $a_1,a_2\in\mathbb{Z}/2$, or a discrete one given by $u\in\mathbb{C}$ and a weight $k\ge 1$), and let $D$ be a real archimedean Whittaker datum for $P$: a function $W$ on real $2\times 2$ matrices, smooth on the set of matrices of nonzero determinant, transforming by $\psi(x)$ under left translation by unipotents and by the central character of $P$ times $|z|$ under scaling, together with an entire-in-$s$ family $(g,u,a,s)\mapsto D.\mathrm{zetaEntire}\,g\,u\,a\,s$ whose values compute the zeta integrals of $W$ divided by the archimedean $\Gamma$-factor of the twist of $P$ by $(u,a)$, satisfying the functional equation, a finite-order bound on each strip for each fixed $g$, and the prescribed decay of the derivatives of $W$ at large and small $y$. Fix $u\in\mathbb{C}$ and $a\in\mathbb{Z}/2$. The assertion is twofold. First, for all real $\sigma_1,\sigma_2$ there are constants $C,A\in\mathbb{R}$ and $N\in\mathbb{N}$, independent of $g$ and $s$, such that for every real $2\times 2$ matrix $g$ with $\det g\neq 0$ and every $s$ with $\sigma_1\le\operatorname{Re} s\le\sigma_2$,
--   $$\|D.\mathrm{zetaEntire}\,g\,u\,a\,s\|\le C\bigl(1+|g_{00}|+|g_{01}|+|g_{10}|+|g_{11}|+|\det g|^{-1}\bigr)^{N}\exp\bigl(A|\operatorname{Im} s|\bigr).$$
--   Second, for every $s\in\mathbb{C}$ the map $M\mapsto D.\mathrm{zetaEntire}\,(\mathrm{of}\,M)\,u\,a\,s$, defined on functions $M:\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{R}$, is continuous on the set of $M$ with $\det(\mathrm{of}\,M)\neq 0$.
--
--   This upgrades the finite-order bound built into the datum, which holds for one matrix at a time, to a bound on vertical strips that is uniform in the matrix up to a polynomial factor in its entries and in $|\det g|^{-1}$, and adds continuity of the entire zeta function in the matrix variable. It is used in the archimedean unfolding step [`LanglandsTunnell.CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul`](thm.html#LanglandsTunnell.CubicInduction.exists_differentiable_unfoldingIntegral_eq_GammaR_mul), where such uniformity licenses integration over the matrix variable; the proof appeals to two-sided Stirling-type bounds for $\Gamma$ on vertical strips.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.exists_norm_zetaEntire_le_mul_pow_mul_exp_and_continuousOn
    {P : RealArchParam} (D : ArchDatumR P) (u : ℂ) (a : ZMod 2) :
    (∀ σ₁ σ₂ : ℝ, ∃ (C A : ℝ) (N : ℕ), ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
        ‖D.zetaEntire g u a s‖ ≤
          C * (1 + |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + |g.det|⁻¹) ^ N * Real.exp (A * |s.im|)) ∧
    ∀ s : ℂ, ContinuousOn (fun M : Fin 2 → Fin 2 → ℝ => D.zetaEntire (Matrix.of M) u a s) ArchR.glSet := by sorry
