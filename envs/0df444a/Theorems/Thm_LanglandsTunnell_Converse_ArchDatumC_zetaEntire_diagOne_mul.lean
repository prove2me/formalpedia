-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumC_zetaEntire_diagOne_mul
-- name    : LanglandsTunnell.Converse.ArchDatumC.zetaEntire_diagOne_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/f939805f-572a-5c11-a658-a2afaaf1a5e1
-- title:
--   Scaling of the entire zeta function under diag(A,1)
-- statement:
--   Let $P$ be a complex archimedean parameter, i.e. data $(u_1,k_1,u_2,k_2)\in\mathbb{C}\times\mathbb{Z}\times\mathbb{C}\times\mathbb{Z}$, and let $D$ be an `ArchDatumC P`: a Whittaker function $W$ on $2\times 2$ complex matrices, smooth on the relevant open set, satisfying the unipotent law $W(n(x)g)=\psi(x)W(g)$ and the central law $W(zg)=\omega_P(z)\lVert z\rVert^{2}W(g)$ for $z\neq0$, together with a function $\zeta^{\mathrm{ent}}=$ `D.zetaEntire` of a matrix, a complex $u$, an integer $k$ and a complex $s$, which is entire in $s$, represents the local zeta integral of $W$ against the quasi-character indexed by $(u,k)$ divided by the archimedean $\Gamma$-factor of `P.twist u k` in the half-plane of convergence, obeys the local functional equation under the Weyl element, and is of finite order in vertical strips with the prescribed decay estimates for $W$. The assertion is: for every $2\times2$ complex matrix $g$ with $\det g\neq0$, every $A\neq0$ in $\mathbb{C}$, every $u\in\mathbb{C}$, $k\in\mathbb{Z}$ and every $s\in\mathbb{C}$,
--   $$\zeta^{\mathrm{ent}}\bigl(\left(\begin{smallmatrix}A&0\\0&1\end{smallmatrix}\right)g,u,k,s\bigr)=\chi_{u,k}(A)^{-1}\,(\lVert A\rVert^{2})^{1-s}\,\zeta^{\mathrm{ent}}(g,u,k,s),$$
--   where $\chi_{u,k}(z)=\lVert z\rVert^{2u}(z/\lVert z\rVert)^{k}$ and $(\lVert A\rVert^{2})^{1-s}$ is the complex power of the real number $\lVert A\rVert^{2}$. The identity is asserted for all $s$, not merely in the region of absolute convergence.
--
--   This is the quasi-invariance of the local zeta integral at a complex place under left translation of the base point by $\operatorname{diag}(A,1)$, transported to the entire normalisation: the factor $\chi_{u,k}(A)^{-1}\lVert A\rVert^{2(1-s)}$ records the change of variable along the torus together with the normalised module of $A$ at a complex place. It is used in the synthesis of cusp forms from Whittaker data, in [`LanglandsTunnell.Converse.CuspSynthesis.exists_isHaarMeasure_torusTransform_eq_of_isJLNice`](thm.html#LanglandsTunnell.Converse.CuspSynthesis.exists_isHaarMeasure_torusTransform_eq_of_isJLNice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumC_zetaEntire_diagOne_mul.lean

import Definitions.Def_LanglandsTunnell_JLConverse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumC.zetaEntire_diagOne_mul {P : ComplexArchParam} (D : ArchDatumC P)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (A : ℂ) (u : ℂ) (k : ℤ) (s : ℂ) (hA : A ≠ 0) (hg : g.det ≠ 0) :
    D.zetaEntire (ArchC.diagOne A * g) u k s =
      (ArchC.quasiChar u k A)⁻¹ * ((‖A‖ ^ 2 : ℝ) : ℂ) ^ (1 - s) * D.zetaEntire g u k s := by sorry
