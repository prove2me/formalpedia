-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_DiscreteFamily_exists_archDatumR_W_eq
-- name    : LanglandsTunnell.Converse.DiscreteFamily.exists_archDatumR_W_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/4010fbd9-14a6-5590-a16c-c2cf6674e985
-- title:
--   Discrete-series Whittaker function as an archimedean datum
-- statement:
--   Let $u_0 \in \mathbb{C}$, let $k_0$ be a natural number and assume $1 \le k_0$. Write $P =$ `RealArchParam.discrete` $u_0\,k_0$ for the discrete real archimedean parameter attached to these data, so that $P$ has central exponent $2u_0$, central sign $k_0 + 1 \in \mathbb{Z}/2$, twist $(u,a) \mapsto$ `discrete` $(u_0+u)\,k_0$ (the sign $a$ being ignored) and archimedean epsilon factor $i^{\,k_0+1}$. The assertion is that there exists a term $D$ of type `ArchDatumR` $P$ whose underlying function $D.W$ is equal to the function `W` $u_0\,k_0$, the explicit discrete-series Whittaker function of exponent $k_0$ and twist $u_0$ on the real $2\times 2$ matrices. Unfolding the structure, this says that `W` $u_0\,k_0$ is smooth, as a function of the matrix entries, on the set `glSet` of matrices of nonzero determinant; satisfies $W(\,!![1,x;0,1]\cdot g) = \psi(x)\,W(g)$ and $W(z \cdot g) = \chi_P(z)\,|z|\,W(g)$ for $z \neq 0$; and is equipped with a zeta package: functions `zetaEntire` $g\,u\,a$ entire in $s$, together with an abscissa $\sigma_0$ such that for $\det g \neq 0$ and $\sigma_0 < \operatorname{Re} s + \operatorname{Re} u$ the integrand `zetaIntegrand` is integrable with integral equal to the archimedean factor of the twisted parameter $P.\mathrm{twist}\,u\,a$ at $s$ times `zetaEntire` $g\,u\,a\,s$, the local functional equation relating `zetaEntire` at $(\mathrm{weyl}\cdot g, -(u+2u_0), a + k_0 + 1, 1-s)$ to $i^{\,k_0+1}$ times `zetaEntire` $g\,u\,a\,s$, finite order in vertical strips, and the two decay bounds for all iterated derivatives along the torus coordinates `diagOneMulCoords` $y\,k$ with $k$ satisfying `IsK`, for $|y| \ge 1$ and for $0 < |y| \le 1$ respectively.
--
--   This is the archimedean existence input at a real place for the discrete series: it records that the explicit discrete-series Whittaker function of weight $k_0$ and twist $u_0$ satisfies all the analytic axioms (equivariance, zeta integrals with their functional equation, growth and decay) required of an archimedean datum for the corresponding parameter. It is used by [`LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero`](thm.html#LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero), which supplies the archimedean component in the converse-theorem construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_DiscreteFamily_exists_archDatumR_W_eq.lean

import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.Converse LanglandsTunnell.Converse.DiscreteFamily

theorem LanglandsTunnell.Converse.DiscreteFamily.exists_archDatumR_W_eq (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) :
    ∃ D : ArchDatumR (RealArchParam.discrete u₀ k₀ hk), D.W = W u₀ k₀ := by sorry
