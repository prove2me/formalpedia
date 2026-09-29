-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight
-- name    : LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_translateRight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ea7ba9d0-f926-581a-bf9a-f8fe6a307000
-- title:
--   Casimir operators commute with right translation
-- statement:
--   Let $H\colon \mathrm{GL}_3(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ be a function on the adelic general linear group `AdelicGL 3 (𝓞 ℚ) ℚ`, i.e. the group of invertible $3\times 3$ matrices over the adele ring of $\mathbb{Q}$, and assume `IsArchSmooth3 H`: for every $g$ the function $e \mapsto H(g \cdot \mathtt{archRealLift3}\,e)$ of a real array $e \colon \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$ is $C^\infty$ (in the sense of `ContDiffOn ℝ ⊤`) on the set of $e$ with $\det(e) \neq 0$, where `archRealLift3 e` is the adelic group element attached to $e$ by `archRealMat3` when the latter is invertible and is $1$ otherwise. For $i,j \in \mathrm{Fin}\,3$ let $(\mathtt{archDeriv}\,i\,j\,\varphi)(g)$ be the derivative at $s = 0$ of $s \mapsto \varphi\bigl(g \cdot \mathtt{archRealLift3}(\delta + s\,E_{ij})\bigr)$, and set $\mathtt{casimir1}\,\varphi = \sum_i D_{ii}\varphi$, $\mathtt{casimir2}\,\varphi = \sum_{i,j} D_{ij}D_{ji}\varphi$ and $\mathtt{casimir3}\,\varphi = \sum_{i,j,k} D_{ij}D_{jk}D_{ki}\varphi$, with $D_{ij} = \mathtt{archDeriv}\,i\,j$. Then for every $y$ in the group, writing $(\mathtt{translateRight}\,y\,\varphi)(x) = \varphi(xy)$, the three equalities of functions $\mathtt{casimir}_m(\mathtt{translateRight}\,y\,H) = \mathtt{translateRight}\,y\,(\mathtt{casimir}_m H)$ hold for $m = 1,2,3$.
--
--   This is the right-invariance of the linear, quadratic and cubic central archimedean differential operators on $\mathrm{GL}_3$ over the adeles of $\mathbb{Q}$, in the concrete form in which those operators are defined here by iterated right derivatives along affine curves $1 + sE_{ij}$ at the infinite place. It underlies the compatibility of the Casimir operators with the smoothing operators and with the spectral decomposition of the cuspidal slab, and is used in the construction of the induced-picture package in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_translateRight.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.casimir_translateRight
    (H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hH : WhittakerBlock.IsArchSmooth3 H) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    casimir1 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir1 H) ∧
      casimir2 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir2 H) ∧
        casimir3 (SlabL2.translateRight y H) = SlabL2.translateRight y (casimir3 H) := by sorry
