-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
-- name    : LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/5afb4992-ca57-55c0-82de-f2f9d3a17c1b
-- title:
--   Right mathfrakgl₃-derivatives at infinity: smoothness, linearity, commutators, translation
-- statement:
--   Write $G =$ `AdelicGL 3 (𝓞 ℚ) ℚ` for $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$; for $e : \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$ let `archRealLift3 e` be the element of $G$ obtained from the real matrix `archRealMat3 e` when the latter is invertible and $1$ otherwise; call $\varphi : G \to \mathbb{C}$ arch-smooth (`IsArchSmooth3`) when for every $g \in G$ the map $e \mapsto \varphi(g\cdot\mathrm{archRealLift3}\, e)$ is $C^\infty$ on $\{e : \det e \neq 0\}$, and set $(\mathrm{archDeriv}\ i\ j\ \varphi)(g) = \frac{d}{ds}\big|_{s=0} \varphi\big(g\cdot\mathrm{archRealLift3}(1 + sE_{ij})\big)$. The theorem is the conjunction of five assertions: (a) for arch-smooth $\varphi$ and all $i,j$, $\mathrm{archDeriv}\ i\ j\ \varphi$ is again arch-smooth; (b) $\mathrm{archDeriv}\ i\ j$ is additive on pairs of arch-smooth functions; (c) $\mathrm{archDeriv}\ i\ j\,(c\varphi) = c\,\mathrm{archDeriv}\ i\ j\,\varphi$ for every $c \in \mathbb{C}$ and every $\varphi$, with no smoothness hypothesis; (d) for arch-smooth $\varphi$ and all $i,j,k,l$, the commutator $\mathrm{archDeriv}\ i\ j\,(\mathrm{archDeriv}\ k\ l\,\varphi) - \mathrm{archDeriv}\ k\ l\,(\mathrm{archDeriv}\ i\ j\,\varphi)$ equals $\delta_{jk}\,\mathrm{archDeriv}\ i\ l\,\varphi - \delta_{li}\,\mathrm{archDeriv}\ k\ j\,\varphi$ (the Kronecker factors being written as `if`-terms); (e) for arch-smooth $\varphi$ and every $y \in G$, the right translate $x \mapsto \varphi(xy)$ is arch-smooth and, for all $g$ and all $i,j$, $(\mathrm{archDeriv}\ i\ j\,(R_y\varphi))(g) = \sum_{p,q} (y_\infty^{-1})_{pi}\,(y_\infty)_{jq}\,(\mathrm{archDeriv}\ p\ q\,\varphi)(gy)$, where $y_\infty \in \mathrm{GL}_3(\mathbb{R})$ is the image of $y$ under `archComponent3` followed by `StandardKernel.realGL`, and the real matrix entries are coerced to $\mathbb{C}$.
--
--   This packages the standard fact that the right derivatives along the elementary matrices $E_{ij}$ define an action of $\mathfrak{gl}_3(\mathbb{R})$ by left-invariant differential operators on functions on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ smooth at the archimedean place, together with the $\mathrm{Ad}(y_\infty^{-1})$-equivariance of these operators under right translation. It is used in the construction of the Casimir elements and their comparison with iterated `archDeriv`s, and in the analysis of smoothing operators on slabs of $L^2$ automorphic functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate :
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ →
      ∀ i j : Fin 3, WhittakerBlock.IsArchSmooth3 (archDeriv i j φ)) ∧
    (∀ φ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → WhittakerBlock.IsArchSmooth3 ψ →
      ∀ i j : Fin 3, archDeriv i j (φ + ψ) = archDeriv i j φ + archDeriv i j ψ) ∧
    (∀ (c : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ i j : Fin 3, archDeriv i j (c • φ) = c • archDeriv i j φ) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ i j k l : Fin 3,
      archDeriv i j (archDeriv k l φ) - archDeriv k l (archDeriv i j φ) =
        (if j = k then archDeriv i l φ else 0) - (if l = i then archDeriv k j φ else 0)) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ),
      WhittakerBlock.IsArchSmooth3 (fun x => φ (x * y)) ∧
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3),
        archDeriv i j (fun x => φ (x * y)) g =
          ∑ p : Fin 3, ∑ q : Fin 3,
            ((((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y))⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) p i *
              ((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) j q : ℂ) *
            archDeriv p q φ (g * y)) := by sorry
