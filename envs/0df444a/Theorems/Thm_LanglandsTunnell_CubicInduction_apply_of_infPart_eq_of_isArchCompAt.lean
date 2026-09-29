-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt
-- name    : LanglandsTunnell.CubicInduction.apply_of_infPart_eq_of_isArchCompAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/f611981e-1bc4-583e-bf28-cfc967f15f0e
-- title:
--   Archimedean value of an idele character through a section of the infinite part
-- statement:
--   Let $\chi \colon (\mathbb{A}_{\mathbb{Q}})^\times \to \mathbb{C}^\times$ be a group homomorphism from the unit group of the adele ring of $\mathbb{Q}$ to $\mathbb{C}^\times$ (no continuity is assumed), and let $E \colon (\mathbb{A}_{\mathbb{Q},\infty})^\times \to (\mathbb{A}_{\mathbb{Q}})^\times$ be a group homomorphism from the units of the infinite adele ring such that for every infinite idele $u$ one has $\mathrm{infPart}(E u) = u$, the image of $E u$ under the projection to the units of the infinite adele ring, and $\mathrm{finPart}(E u) = 1$, the image of $E u$ under the projection to the units of the finite adele ring. Let $t \in \mathbb{C}$ and $e \in \mathbb{Z}$, and assume that for every real infinite place $w$ of $\mathbb{Q}$ the predicate `IsArchCompAt` holds for $\chi$, $w$, $t$, $e$, that is, for every unit $x$ of the completion $\mathbb{Q}_w$, $$\chi\bigl(\mathrm{archUnitHom}_w(x)\bigr) = \lVert x\rVert^{\,m_w t}\cdot\bigl(\iota_w(x)/\lVert x\rVert\bigr)^{e},$$ where $m_w$ is the multiplicity of $w$, $\iota_w$ is `extensionEmbedding` of $\mathbb{Q}_w$ into $\mathbb{C}$, and $\mathrm{archUnitHom}_w$ sends a unit of $\mathbb{Q}_w$ to the idele concentrated at $w$. Then for every infinite idele $z$ and every real infinite place $v$, writing $z_v$ for the component of $z$ at $v$, $$\chi(E z) = \lVert z_v\rVert^{\,m_v t}\cdot\bigl(\iota_v(z_v)/\lVert z_v\rVert\bigr)^{e}.$$
--
--   This is the evaluation of a global character of the ideles of $\mathbb{Q}$, given by its infinity type $(t,e)$ at the archimedean place, on an idele supported at infinity, read through a section $E$ of the infinite part. It is used throughout the converse-theorem input of the Langlands–Tunnell step, in particular in the identities expressing the functional equations and zeta integrals attached to a cubic induction datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt.lean

import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.apply_of_infPart_eq_of_isArchCompAt
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (t : ℂ) (e : ℤ) (hχ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ χ v t e)
    (z : (InfiniteAdeleRing ℚ)ˣ) (v : InfinitePlace ℚ) (hv : v.IsReal) :
    ((χ (E z) : ℂˣ) : ℂ) =
      ((‖(z : InfiniteAdeleRing ℚ) v‖ : ℂ) ^ ((v.mult : ℂ) * t)) *
        (NumberField.InfinitePlace.Completion.extensionEmbedding v ((z : InfiniteAdeleRing ℚ) v) /
            (‖(z : InfiniteAdeleRing ℚ) v‖ : ℂ)) ^ e := by sorry
