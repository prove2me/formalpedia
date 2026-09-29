-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa
-- name    : MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/36ed974d-6cfd-5c18-9185-2d836b33538b
-- title:
--   Haar measure on GL₂(ℝ) in Iwasawa coordinates
-- statement:
--   Let $\mathrm{GL}_2(\mathbb{R})$ and the subgroup $K =$ `rowIsometrySubgroup ℝ` be equipped with measurable structures that are the Borel structures of their topologies, where $K$ consists of those $k \in \mathrm{GL}_2(\mathbb{R})$ with $|\det k| = 1$ such that $\|xk_{00} + yk_{10}\|^2 + \|xk_{01} + yk_{11}\|^2 = \|x\|^2 + \|y\|^2$ for all real $x, y$, i.e. right multiplication by $k$ preserves the Euclidean norm of row vectors. Let $\mu$ be any Haar measure on $\mathrm{GL}_2(\mathbb{R})$ and $\nu$ any Haar measure on $K$. The assertion is that there exists $c \in \mathbb{R}_{\geq 0}$ with $c > 0$ such that $\mu = c \cdot \Phi_* \lambda$, where $\lambda$ is the product of $\nu$ with the Lebesgue measure on $\mathbb{R}^3$ restricted to $\mathbb{R} \times (0,\infty) \times (0,\infty)$ and multiplied by the density $(x,y,t) \mapsto y^{-2}t^{-1}$, and where $\Phi\bigl((x,y,t),k\bigr) = \bigl(\begin{smallmatrix} ty & tx \\ 0 & t\end{smallmatrix}\bigr)\, k$ when $y > 0$ and $t > 0$ (the matrix being formed by `upperUnit (t*y) (t*x) t`), and $\Phi\bigl((x,y,t),k\bigr) = k$ on the complementary null set.
--
--   This is the classical integration formula for a Haar measure of $\mathrm{GL}_2(\mathbb{R})$ in Iwasawa ($B \cdot K$) coordinates, $dg = c\, y^{-2}\,dx\,dy\,t^{-1}\,dt\,dk$, stated for an arbitrary pair of Haar measures on the group and on the orthogonal subgroup, so that the constant is left unspecified. It is used in the Langlands–Tunnell converse-theorem material to convert archimedean integrals over Siegel sets into iterated integrals in the coordinates $(x,y,t,k)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa.lean

import Mathlib
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

theorem MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_iwasawa
    [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
    [MeasurableSpace (rowIsometrySubgroup ℝ)] [BorelSpace (rowIsometrySubgroup ℝ)]
    (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure]
    (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun q : (ℝ × ℝ × ℝ) × rowIsometrySubgroup ℝ =>
          (if h : 0 < q.1.2.1 ∧ 0 < q.1.2.2 then
              upperUnit (q.1.2.2 * q.1.2.1) (q.1.2.2 * q.1.1) q.1.2.2
                (mul_pos h.2 h.1).ne' h.2.ne'
            else 1) * (q.2 : GL (Fin 2) ℝ))
        (((volume.restrict (Set.univ ×ˢ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).withDensity
            (fun q => ENNReal.ofReal ((q.2.1 ^ 2)⁻¹ * q.2.2⁻¹))).prod ν) := by sorry
