-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero
-- name    : LanglandsTunnell.Converse.exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/62628195-9549-5699-aaf4-80fbf3576c81
-- title:
--   Non-vanishing weight-one archimedean datum at the odd Artin parameter
-- statement:
--   The assertion is closed: no variables, no hypotheses. Write $P =$ `RealArchParam.oddArtin`, the principal real archimedean parameter `.principal 0 0 0 1`, i.e. exponents $u_1 = u_2 = 0$ and signs $a_1 = 0$, $a_2 = 1$ (so central exponent $0$, central sign $1$, and $\varepsilon$-factor $\mathrm{signEpsilon}(0)\cdot\mathrm{signEpsilon}(1)$). The theorem states that there exists $d$ : `ArchDatumR` $P$ — that is, a function $W = d.W$ on $2\times 2$ real matrices with values in $\mathbb{C}$, subject to the laws packaged in `ArchDatumR`: smoothness of $W$ to all orders on the invertible locus, the unipotent law $W(u(x)g) = \psi(x)W(g)$, the central law $W(zg) = \mathrm{centralChar}_P(z)\,|z|\,W(g)$ for $z \ne 0$, an entire function $\mathrm{zetaEntire}$ together with integrability of the zeta integrand and the identity $\int_{\mathbb{R}} \mathrm{zetaIntegrand}\,W\,g\,u\,a\,s = (P.\mathrm{twist}\,u\,a).\mathrm{archFactor}(s)\cdot \mathrm{zetaEntire}\,g\,u\,a\,s$ to the right of an abscissa, the functional equation relating $\mathrm{zetaEntire}$ at $\mathrm{weyl}\cdot g$, shifted exponent and sign, and $1-s$ to its value at $g, u, a, s$ through the $\varepsilon$-factor of the twisted parameter, finite order of $\mathrm{zetaEntire}$ in vertical strips, and decay bounds for all iterated derivatives of $W$ in the Iwasawa coordinate $y$, uniformly over the maximal compact, both for $|y| \ge 1$ with arbitrary polynomial rate and for $0 < |y| \le 1$ (these laws are summarised here) — such that three further conditions hold. First, for every $r$ in the subgroup `rowIsometrySubgroup₀` of $GL_2(\mathbb{R})$ and every $x \in GL_2(\mathbb{R})$, $W(xr) = \mathrm{archWeightChar}_{\mathbb{R}}(1)(r)\cdot W(x)$, the value of the weight-one character `archWeightCharℝ 1` being taken in $\mathbb{C}$. Second, for every $x \in GL_2(\mathbb{R})$, the function $z \mapsto (\operatorname{Im} z)^{-1}\,W\bigl(x\cdot \mathrm{iwasawaSectionGL}(z)\bigr)$, where $\mathrm{iwasawaSectionGL}(z)$ is the invertible matrix $\begin{pmatrix}\operatorname{Im} z & \operatorname{Re} z\\ 0 & 1\end{pmatrix}$, is differentiable as a map of complex manifolds from the upper half-plane to $\mathbb{C}$, both sides carried by the self-model of $\mathbb{C}$; that is, the normalised restriction to the upper half-plane is holomorphic. Third, $W(g) \ne 0$ for some $g \in GL_2(\mathbb{R})$.
--
--   This provides the archimedean input at a real place in weight one: a Whittaker-type function at the odd Artin parameter $1 \oplus \mathrm{sgn}$ which transforms by the weight-one character under the relevant compact subgroup, restricts holomorphically to the upper half-plane after the standard normalisation, and is not identically zero. It strengthens the corresponding existence statement without the non-vanishing clause, and is used in the converse-theorem step that produces an arithmetic genuine cusp form realising a given eigenvalue table, where a datum of this kind is supplied at every real place; the non-vanishing clause excludes the degenerate datum $W = 0$, which satisfies the other two conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem LanglandsTunnell.Converse.exists_archDatumR_oddArtin_archWeightChar_one_mdifferentiable_W_ne_zero :
    ∃ d : ArchDatumR RealArchParam.oddArtin,
      (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        d.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ 1 r : ℂ) * d.W (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      (∀ (x : GL (Fin 2) ℝ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            d.W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∃ g : GL (Fin 2) ℝ, d.W g ≠ 0 := by sorry
