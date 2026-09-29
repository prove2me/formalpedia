-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_foldr_archDeriv_mul_right_eq_sum
-- name    : LanglandsTunnell.CubicInduction.foldr_archDeriv_mul_right_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/437f9955-9421-5149-9601-6c657468edd6
-- title:
--   Right translation of archimedean derivative words on GL₃
-- statement:
--   Work with $G = \mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$ (that is, `AdelicGL 3 (𝓞 ℚ) ℚ`, the general linear group of $3\times 3$ matrices over the adeles), and for $i,j \in \{0,1,2\}$ let `WhittakerBlock.archDeriv i j` send $\varphi : G \to \mathbb{C}$ to the function $g \mapsto \frac{d}{ds}\big|_{s=0}\varphi\big(g\cdot \mathrm{archRealLift3}(I + s e_{ij})\big)$, where $\mathrm{archRealLift3}$ embeds a real $3\times 3$ matrix into $G$ whenever the resulting element is a unit (and is $1$ otherwise). A word $w$ in `List (Fin 3 × Fin 3)` is turned into an iterated such derivative by right-folding, so that $w = [\,(i_1,j_1),\dots,(i_r,j_r)\,]$ acts as $\mathrm{archDeriv}\,i_1 j_1 \circ \cdots \circ \mathrm{archDeriv}\,i_r j_r$. The assertion: for every word $w_0$ and every $k_0 \in G$ there exist an $n \in \mathbb{N}$, coefficients $c : \mathrm{Fin}\,n \to \mathbb{C}$ and words $w_1,\dots,w_n$, each of the same length as $w_0$, depending only on $w_0$ and $k_0$, such that for every $u : G \to \mathbb{C}$ satisfying [`WhittakerBlock.IsArchSmooth3 u`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) (for each $g$, the function $e \mapsto u(g\cdot\mathrm{archRealLift3}\,e)$ on real $3\times 3$ matrices is $C^\infty$ on the locus $\det e \neq 0$) and every $g \in G$, the $w_0$-derivative of $u$ evaluated at $g k_0$ equals $\sum_i c_i$ times the $w_i$-derivative of the right translate $g \mapsto u(g k_0)$, evaluated at $g$.
--
--   This is the commutation of right translation with words of archimedean right-invariant derivatives, in the form of an adjoint-type expansion: translating by $k_0$ replaces a derivative word by a finite linear combination of words of the same length with coefficients independent of the function. It is used in the study of archimedean growth of Whittaker functions on $\mathrm{GL}_3$, being cited in the derivation of flat regular-singular systems from the Casimir relations and in the bound for translated Whittaker sums along diagonal rays.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_foldr_archDeriv_mul_right_eq_sum.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.CubicInduction.foldr_archDeriv_mul_right_eq_sum
    (w₀ : List (Fin 3 × Fin 3)) (k₀ : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (ws : Fin n → List (Fin 3 × Fin 3)),
      (∀ i, (ws i).length = w₀.length) ∧
      ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 u → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w₀ (g * k₀) =
          ∑ i, c i * List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => u (g * k₀)) (ws i) g := by sorry
