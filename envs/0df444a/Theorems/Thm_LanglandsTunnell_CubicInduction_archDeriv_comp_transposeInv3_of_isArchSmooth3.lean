-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3
-- name    : LanglandsTunnell.CubicInduction.archDeriv_comp_transposeInv3_of_isArchSmooth3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/70fd89cd-4457-5178-ae60-b75d2848e575
-- title:
--   Transpose-inverse involution negates archimedean derivatives, swapping indices
-- statement:
--   Let $G = \mathrm{GL}_3$ over the adele ring of $\mathbb{Q}$, i.e. `AdelicGL 3 (𝓞 ℚ) ℚ`, the group of units of the ring of $3\times 3$ matrices over $\mathbb{A}_\mathbb{Q}$. For a real array $e : \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$, `archRealLift3 e` denotes the element of $G$ given by the unit attached to the adelic matrix `archRealMat3 e` when that matrix is invertible, and $1$ otherwise; and for $i,j \in \mathrm{Fin}\,3$ and $\varphi : G \to \mathbb{C}$, `archDeriv i j φ` is the function sending $g \in G$ to the derivative at $s = 0$ of $s \mapsto \varphi\bigl(g \cdot \mathrm{archRealLift3}(\mathbf{1} + s E_{ij})\bigr)$, where $\mathbf{1} + sE_{ij}$ is the real array with entries $\delta_{ab} + s\,[a = i][b = j]$. Let $\varphi : G \to \mathbb{C}$ satisfy `IsArchSmooth3 φ`: for every $g \in G$ the map $e \mapsto \varphi(g \cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on the set of real arrays $e$ with $\det(e) \neq 0$. Let $i, j \in \mathrm{Fin}\,3$ and $g \in G$, and let $\mathrm{transposeInv3}(x) = (x^{-1})^{\mathsf{T}}$ be the transpose-inverse involution of $G$. Then the $(i,j)$-derivative of $\varphi \circ \mathrm{transposeInv3}$ at $g$ equals minus the $(j,i)$-derivative of $\varphi$ at $\mathrm{transposeInv3}(g)$.
--
--   This is the infinitesimal form of the transpose-inverse involution of $\mathrm{GL}_3$, namely the automorphism $X \mapsto -X^{\mathsf{T}}$ of $\mathfrak{gl}_3$, expressed for the archimedean right derivatives along elementary matrices. It is used to transport archimedean smoothness and the associated centre conditions across the involution, and is cited by [`LanglandsTunnell.CubicInduction.archPackage_comp_transposeInv3_of_isCentreFinite`](thm.html#LanglandsTunnell.CubicInduction.archPackage_comp_transposeInv3_of_isCentreFinite) and [`LanglandsTunnell.CubicInduction.isCentreFinite_comp_transposeInv3_of_isArchSmooth3`](thm.html#LanglandsTunnell.CubicInduction.isCentreFinite_comp_transposeInv3_of_isArchSmooth3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.archDeriv_comp_transposeInv3_of_isArchSmooth3
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j (fun x => φ (transposeInv3 x)) g =
      -WhittakerBlock.archDeriv j i φ (transposeInv3 g) := by sorry
