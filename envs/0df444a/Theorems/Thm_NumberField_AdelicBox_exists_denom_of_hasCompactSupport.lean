-- Prove2me | Theorems.Thm_NumberField_AdelicBox_exists_denom_of_hasCompactSupport
-- name    : NumberField.AdelicBox.exists_denom_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/91f54ba5-7437-55bb-b041-139d4fa7151f
-- title:
--   Bounded denominators on the compact support of a finite-adelic function
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal O_F$ and finite adele ring $\mathbb A_F^{\mathrm{fin}} =$ `FiniteAdeleRing (𝓞 F) F`, and let $h\colon \mathbb A_F^{\mathrm{fin}} \to \mathbb C$ be a function whose support is compactly supported in the sense of `HasCompactSupport`, i.e. the closure of $\{z : h(z) \neq 0\}$ is compact. The assertion is that there exists $d \in \mathcal O_F$, $d \neq 0$, such that for every $\kappa \in F$ whose image under the algebra map $F \to \mathbb A_F^{\mathrm{fin}}$ satisfies $h(\iota(\kappa)) \neq 0$, there is $a \in \mathcal O_F$ with $d\kappa = a$ as an identity in $F$ (both $d$ and $a$ being taken through the inclusion $\mathcal O_F \hookrightarrow F$). In other words, a single nonzero denominator $d$ works simultaneously for all principal points at which $h$ is nonvanishing: the set of such $\kappa$ is contained in the fractional ideal $d^{-1}\mathcal O_F$.
--
--   This is the support-confinement, or bounded-denominator, step in adelic Fourier analysis: a compactly supported function on the finite adeles can be nonzero on principal points only inside one fractional ideal $d^{-1}\mathcal O_F$, which is a free $\mathcal O_F$-module of rank one. It is used in the proof of [`NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet`](thm.html#NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet), where it reduces a sum over principal adelic points to a lattice sum governed by the archimedean factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_exists_denom_of_hasCompactSupport.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicBox IsDedekindDomain

theorem NumberField.AdelicBox.exists_denom_of_hasCompactSupport
    {F : Type*} [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ κ : F, h (algebraMap F (FiniteAdeleRing (𝓞 F) F) κ) ≠ 0 →
      ∃ a : 𝓞 F, (d : F) * κ = a := by sorry
