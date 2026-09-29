-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
-- name    : NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/963d2c48-b945-5561-895b-4f90c4a661c3
-- title:
--   A continuous homomorphic section of the idele norm
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$, together with its ring of integers $\mathcal{O}_F$). The assertion is that there exists a monoid homomorphism $s$ from $\mathbb{R}_{\ge 0}^{\times}$, the group of units of the nonnegative reals — i.e. the multiplicative group of strictly positive reals — to the unit group of the adele ring $\mathbb{A}_F = \mathbb{A}_{\infty,F} \times \mathbb{A}_{\mathrm{fin},F}$ of $F$, such that three conditions hold: $s$ is continuous for the adelic topology on the units; for every $r \in \mathbb{R}_{\ge 0}^{\times}$ one has $\mathrm{ideleNorm}_F(s\,r) = r$, where $\mathrm{ideleNorm}_F(x)$ is by definition the value at $x$ of the distributive Haar character $\mathrm{distribHaarChar}$ of the additive group $\mathbb{A}_F$, viewed as a nonnegative real and then as a real number, that is, the scaling factor by which multiplication by the idele $x$ distorts an additive Haar measure on $\mathbb{A}_F$; and for every $r$ the second component of the underlying adele of $s\,r$, namely its finite-adelic component, is equal to $1$.
--
--   This is the standard splitting of the idele norm: the exact sequence $1 \to \mathbb{A}_F^1 \to \mathbb{A}_F^{\times} \to \mathbb{R}_{>0} \to 1$ admits a continuous homomorphic section supported at the archimedean places, whence in particular the norm is surjective and $\mathbb{A}_F^{\times} \cong \mathbb{A}_F^1 \times \mathbb{R}_{>0}$ as topological groups. It is used throughout the Tate-style analysis of global zeta integrals and of automorphic forms, for instance in the decomposition of adelic Haar measure and in growth estimates for cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal
open scoped NNReal

theorem NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq
    (F : Type) [Field F] [NumberField F] :
    ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ, Continuous s ∧
      (∀ r : ℝ≥0ˣ, ideleNorm F (s r) = ((r : ℝ≥0) : ℝ)) ∧
      ∀ r : ℝ≥0ˣ, ((s r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by sorry
