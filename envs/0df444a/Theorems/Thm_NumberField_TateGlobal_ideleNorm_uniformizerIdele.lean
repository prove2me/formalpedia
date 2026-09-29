-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
-- name    : NumberField.TateGlobal.ideleNorm_uniformizerIdele
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/5eb789c0-adb6-5359-bf7f-f5f526441893
-- title:
--   Idele norm of a uniformizer idele is (Nv)⁻¹
-- statement:
--   Let $F$ be a number field and let $v$ be a point of the height one spectrum of the ring of integers $\mathcal{O}_F$, i.e. a nonzero prime ideal $v.\mathrm{asIdeal}$. Consider the unit `uniformizerIdele F v` of the adele ring of $F$: at the finite part it is the unit of the finite adele ring built by `localUnit` from `uniformizerUnit`, namely the family whose $v$-component is the image in the completion $F_v$ of the chosen uniformizer `uniformizer v` of $\mathcal{O}_F$ at $v$ (a unit of $F_v$ because its valuation is nonzero) and whose component at every other finite place is $1$; its infinite part is $1$, since `finIncl` sends a finite adele $x$ to the pair $(1, x)$. The quantity `ideleNorm F` of a unit of the adele ring is the value at that unit of the distributive Haar character of the adele ring of $F$, viewed as a real number, so the scaling factor by which multiplication by the unit distorts Haar measure. The assertion is that this number equals $(\#(\mathcal{O}_F/v.\mathrm{asIdeal}))^{-1}$, the inverse of the absolute norm `Ideal.absNorm` of $v.\mathrm{asIdeal}$, cast to $\mathbb{R}$.
--
--   This is the local computation of the module of an idele in Tate's theory, in the special case of the idele supported at a single finite place with a uniformizer there; it gives the factor $(Nv)^{-1}$ that governs the Euler factor at $v$. It is used throughout the global zeta-integral and Hecke-eigenfunction parts of the development, where growth and recursion estimates are indexed by powers of uniformizer ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.TateGlobal.ideleNorm_uniformizerIdele (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by sorry
