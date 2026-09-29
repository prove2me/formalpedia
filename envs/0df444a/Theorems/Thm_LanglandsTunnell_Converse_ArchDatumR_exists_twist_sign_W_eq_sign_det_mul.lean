-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_sign_W_eq_sign_det_mul
-- name    : LanglandsTunnell.Converse.ArchDatumR.exists_twist_sign_W_eq_sign_det_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/3b1a216b-285b-577b-bfc9-d7c6b0e0f2bf
-- title:
--   Sign twist of an archimedean Whittaker datum
-- statement:
--   Let $P$ be a real archimedean parameter (either `principal u₁ a₁ u₂ a₂` with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or `discrete u k` with $1\le k$), and let $D$ be an archimedean Whittaker datum for $P$, i.e. a function $W:M_2(\mathbb{R})\to\mathbb{C}$ that is smooth on the invertible locus, satisfies the unipotent law $W(n(x)g)=\psi(x)W(g)$ and the central law $W(zg)=\omega_P(z)\,|z|\,W(g)$ for $z\neq 0$, together with a family of entire zeta functions representing the integrals $\int_{\mathbb{R}}$ against the archimedean factor of $P$ twisted by $(u,a)$, their functional equation with the $\varepsilon$-factor of the twisted parameter, finite-order growth in vertical strips, and the decay bounds at large and small $y$. The assertion is that there exists an archimedean Whittaker datum $D'$ for the parameter $P$ twisted by $(0,1)$ (so both signs $a_i$ are shifted by $1$ in the principal case, and the discrete parameter is unchanged) such that: (i) $D'.W(g)=\mathrm{sign}(\det g)\,D.W(g)$ for all $g\in M_2(\mathbb{R})$, the sign being $-1,0,1$; (ii) if $D$ satisfies the Casimir eigenequation $\mathrm{matrixCasimir}\,(D.W)(x)=\lambda_P\,D.W(x)$ at all $x$ with $\det x\neq 0$, then $D'$ satisfies the corresponding equation with the Laplace eigenvalue of the twisted parameter; (iii) for every $k\in\mathbb{Z}$, if $D.W(xr)=\mathrm{archWeightChar}_{\mathbb{R}}(k)(r)\,D.W(x)$ for all $r$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $\mathrm{GL}_2(\mathbb{R})$ and all $x\in\mathrm{GL}_2(\mathbb{R})$, then the same weight-$k$ law holds for $D'.W$; and (iv) if $D.W$ is nonzero at some $g\in\mathrm{GL}_2(\mathbb{R})$, then so is $D'.W$.
--
--   This is the archimedean counterpart of twisting an automorphic representation of $\mathrm{GL}(2)$ by the sign character of the determinant: the Whittaker function of $\pi\otimes\mathrm{sgn}(\det)$ is $\mathrm{sign}(\det)$ times that of $\pi$, and the zeta integrals pick up $\mathrm{sgn}(y)$, which is exactly the shift $a\mapsto a+1$ of the archimedean parameter. It is used in the converse-theorem part of the Langlands–Tunnell argument to identify the archimedean parameter attached to a weight-one cuspidal constituent up to a sign twist, and to transport the Casimir eigenvalue, the weight law and non-vanishing across that twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_sign_W_eq_sign_det_mul.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem LanglandsTunnell.Converse.ArchDatumR.exists_twist_sign_W_eq_sign_det_mul
    (P : RealArchParam) (D : ArchDatumR P) :
    ∃ D' : ArchDatumR (P.twist 0 1),
      (∀ g : Matrix (Fin 2) (Fin 2) ℝ, D'.W g = ((SignType.sign g.det : ℝ) : ℂ) * D.W g) ∧
      (ArchCasimir.IsCasimirEigen D → ArchCasimir.IsCasimirEigen D') ∧
      (∀ k : ℤ, (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) →
        (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D'.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D'.W (x : Matrix (Fin 2) (Fin 2) ℝ))) ∧
      ((∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) → ∃ g : GL (Fin 2) ℝ, D'.W g ≠ 0) := by sorry
