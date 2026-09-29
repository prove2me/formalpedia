-- Prove2me | Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
-- name    : M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/3985259d-8b5c-5e01-a76a-c44d3cd9621c
-- title:
--   Idelic norm of a uniformizer idele
-- statement:
--   Let $K$ and $M$ be number fields with $M$ an algebra over $K$, and let $\mathfrak P$ be a height-one prime of $\mathcal O_M$, with $v := \mathfrak P \cap \mathcal O_K$ its contraction to $\mathcal O_K$ (written `𝔓.under (𝓞 K)`). Write $f :=$ `inertiaDeg'` of $\mathfrak P$ over $v$. For a number field $F$ and a finite place $u$, the uniformizer idele `uniformizerIdele F u` is the unit of the adele ring $\mathbb A_F$ whose infinite component is $1$ and whose finite component is the function taking at $u$ the image of the chosen uniformizer of $u$ in the completion $F_u$ and the value $1$ at every other finite place. The assertion is the existence of a unit $t$ of the completion $K_v$ with $\mathrm{v}(t) = 1$ for the canonical valuation, such that the idelic norm attached to the adele base change `genuineBaseChange K M` — that is, `Units.map` applied to the algebra norm $\mathbb A_M \to \mathbb A_K$ for the ring homomorphism `genuineβ K M` — sends `uniformizerIdele M 𝔓` to the product of the $f$-th power of `uniformizerIdele K v` with the idele having component $t$ at $v$ and $1$ elsewhere. No unramifiedness hypothesis is imposed.
--
--   This is the place-by-place computation of the relative idelic norm of a uniformizer idele: up to a unit at $v$, the norm of $\varpi_{\mathfrak P}$ is $\varpi_v^{f(\mathfrak P\mid v)}$. It is used in the comparison of Hecke eigenvalues of an automorphic form with those of its base change, where Hecke operators at finite places are expressed through uniformizer ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit.lean

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
    (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (𝔓 : HeightOneSpectrum (𝓞 M)) :
    ∃ t : ((𝔓.under (𝓞 K)).adicCompletion K)ˣ, Valued.v (t : (𝔓.under (𝓞 K)).adicCompletion K) = 1 ∧
      (M4aHerbrand.GenuineDescent.genuineBaseChange K M).idelicNorm (AutomorphicForm.uniformizerIdele M 𝔓) =
        AutomorphicForm.uniformizerIdele K (𝔓.under (𝓞 K)) ^ ((𝔓.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓.asIdeal) *
          Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
            (NumberField.AdelicLevel.localUnit (𝓞 K) K (𝔓.under (𝓞 K)) t) := by sorry
