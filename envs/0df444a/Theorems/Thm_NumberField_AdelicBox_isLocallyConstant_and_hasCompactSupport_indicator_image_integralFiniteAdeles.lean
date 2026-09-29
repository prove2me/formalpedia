-- Prove2me | Theorems.Thm_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
-- name    : NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/0b3e388d-8551-5497-9257-bd6627df42d1
-- title:
--   Indicator of the coset k+dwidehat𝒪_F is locally constant, compactly supported
-- statement:
--   Let $F$ be a number field, let $d$ be a nonzero element of its ring of integers $\mathcal O_F$, and let $k \in F$. Consider the finite adele ring $\mathbb A_F^f =$ `FiniteAdeleRing (𝓞 F) F` and inside it the set `integralFiniteAdeles (𝓞 F) F` of those finite adeles $x$ whose component $x_v$ lies in the valuation ring $\mathcal O_v$ of $F_v$ for every $v$ in the height-one spectrum of $\mathcal O_F$, i.e. $\widehat{\mathcal O}_F = \prod_v \mathcal O_v$. Let $S$ be the image of this set under the map $z \mapsto k + d z$, where $k$ and $d$ are transported into $\mathbb A_F^f$ along the structure map $F \to \mathbb A_F^f$; thus $S = k + d\,\widehat{\mathcal O}_F$. The assertion is the conjunction of two statements about the indicator function of $S$ with values in $\mathbb C$, that is, the function equal to $1$ on $S$ and to $0$ off $S$: it is locally constant on $\mathbb A_F^f$, and it has compact support.
--
--   This records that the characteristic function of a principal coset $k + d\,\widehat{\mathcal O}_F$ is a basic Schwartz–Bruhat function on the finite adeles. It is used in the adelic Fourier-analytic part of the development, where sums and Fourier transforms of Schwartz–Bruhat functions are analysed via pure tensors whose finite components are such indicators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

theorem NumberField.AdelicBox.isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    IsLocallyConstant (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
      ∧ HasCompactSupport (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) := by sorry
