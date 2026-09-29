-- Prove2me | Theorems.Thm_HopfAlgebra_exists_signTwist_linearEquiv_padicInt_of_odd
-- name    : HopfAlgebra.exists_signTwist_linearEquiv_padicInt_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/95df7553-fbe7-5a96-96f6-bd09ce7e3aa2
-- title:
--   Quadratic twist of a finite flat ℤₚ-Hopf algebra by a unit
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $d_0 \in \mathbb{Z}_p$ be a unit, and let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. Put $P_- := \mathrm{inv}(2) \cdot (\mathrm{id} - S)$, where $S$ denotes the antipode and $\mathrm{inv}(2)$ the ring inverse of $2$ in $\mathbb{Z}_p$ (a unit, since $p$ is odd). The assertion is that there exists a type $H'$, equipped with a commutative ring structure and a $\mathbb{Z}_p$-Hopf algebra structure, again finite and flat over $\mathbb{Z}_p$ and with cocommutative comultiplication, together with a $\mathbb{Z}_p$-linear isomorphism $e \colon H' \xrightarrow{\sim} H$ satisfying: $e(1) = 1$; $e(ab) = e(a)e(b) + (d_0 - 1)\,P_-(e a)\,P_-(e b)$ for all $a, b \in H'$; $\varepsilon_H(e(a)) = \varepsilon_{H'}(a)$ for all $a$; $e(S_{H'}(a)) = S_H(e(a))$ for all $a$; and $(e \otimes e)(\Delta_{H'} a) = \Delta_H(e a) + (\mathrm{inv}(d_0) - 1)\,(P_- \otimes P_-)(\Delta_H(e a))$ for all $a$. Thus $e$ is linear but in general neither a ring nor a coalgebra map: the displayed identities record exactly how the structure maps of $H'$ differ from those of $H$.
--
--   This is the Hopf-algebra incarnation of the quadratic twist of a finite flat commutative group scheme over $\mathbb{Z}_p$ by a unit $d_0$: the twisted multiplication and comultiplication are obtained from those of $H$ by the explicit $d_0$-corrections on the $(-1)$-eigenspace of the antipode. It is used by [`HopfAlgebra.exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare`](thm.html#HopfAlgebra.exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare), where the twisted Hopf algebra is compared with the original on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_signTwist_linearEquiv_padicInt_of_odd.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped TensorProduct in

theorem HopfAlgebra.exists_signTwist_linearEquiv_padicInt_of_odd
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ℤ_[p] H'),
      Module.Finite ℤ_[p] H' ∧ Module.Flat ℤ_[p] H' ∧ Coalgebra.IsCocomm ℤ_[p] H' ∧
      ∃ e : H' ≃ₗ[ℤ_[p]] H,
        e 1 = 1 ∧
        (∀ a b : H', e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b))) ∧
        (∀ a : H', (Coalgebra.counit (e a) : ℤ_[p]) = Coalgebra.counit a) ∧
        (∀ a : H', e (HopfAlgebra.antipode ℤ_[p] a) = HopfAlgebra.antipode ℤ_[p] (e a)) ∧
        (∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                    (Coalgebra.comul a)
              = Coalgebra.comul (e a)
                + (Ring.inverse d₀ - 1) •
                    (TensorProduct.map Pm Pm) (Coalgebra.comul (e a))) := by sorry
