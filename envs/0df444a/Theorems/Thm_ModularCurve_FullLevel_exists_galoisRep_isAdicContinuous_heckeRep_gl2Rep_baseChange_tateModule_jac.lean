-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac
-- name    : ModularCurve.FullLevel.exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/16bf8621-50ee-518b-a439-67d11348dd9a
-- title:
--   Finite freeness and base-changed actions on T_λ(Jac(q,M'))
-- statement:
--   Let $q$ be a prime, let $M'$ be a nonzero natural number and let $\lambda$ be a prime. Write $\mathrm{Jac}(q,M')$ for the group `Jac q M'` of functions from `Idx q` to $J_H(q^2M')$ for the level subgroup `levelH q M'`, and let $T=$ [`TateModule lam (Jac q M')`](def/EllipticCurve_TateModule.html#L15) be the group of sequences $(x_n)$ in $\mathrm{Jac}(q,M')$ with $\lambda^n x_n=0$ and $\lambda x_{n+1}=x_n$ for all $n$. The assertion is threefold: $T$ is a finite $\mathbb Z_\lambda$-module; $T$ is a free $\mathbb Z_\lambda$-module; and for every commutative local ring $O'$ that is a $\mathbb Z_\lambda$-algebra with $\lambda$ in its maximal ideal there exist a monoid homomorphism $\rho$ from the group of $\mathbb Q$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb Q$, a ring homomorphism $T$ from `HeckeAlg` $=\mathbb Z[X_\ell:\ell\ \text{prime}]$, and a monoid homomorphism $G$ from $\mathrm{GL}_2(\mathbb Z/q)$, all into $\mathrm{End}_{O'}(O'\otimes_{\mathbb Z_\lambda}T)$, such that on pure tensors $\rho(\sigma)(a\otimes x)=a\otimes \mathrm{tateGal}(\sigma)x$, $T(t)(a\otimes x)=a\otimes\mathrm{tateHecke}(t)x$ and $G(g)(a\otimes x)=a\otimes\mathrm{tateGL2}(g)x$; such that $T$ kills `heckeGen` $\ell$ for every prime $\ell$ dividing $qM'$; and such that $\rho$ is adically continuous in the sense that for each $n$ there is a finite subextension $L$ of $\mathbb Q$ in $\mathrm{AlgebraicClosure}\,\mathbb Q$ with $\rho(\sigma)v-v\in \mathfrak m_{O'}^n\cdot(O'\otimes T)$ for all $v$ and all $\sigma$ fixing $L$ pointwise.
--
--   This supplies the carrier of the $\lambda$-adic Tate module at full level $q$ over $\Gamma_0(M')$ together with three of its structures — the Galois action, the Hecke action with the generators at primes dividing $qM'$ annihilated, and the action of $\mathrm{GL}_2(\mathbb F_q)$ — after base change to a local $\mathbb Z_\lambda$-algebra. It is used in the assembly of the full-level Tate-module data and in the construction of Hecke ring homomorphisms with prescribed behaviour on the generators; the finiteness, freeness and continuity inputs come from the corresponding statements for $J_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_GaloisRep_Adic
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel TensorProduct

theorem ModularCurve.FullLevel.exists_galoisRep_isAdicContinuous_heckeRep_gl2Rep_baseChange_tateModule_jac
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] :
    Module.Finite ℤ_[lam] (TateModule lam (Jac q M')) ∧
    Module.Free ℤ_[lam] (TateModule lam (Jac q M')) ∧
    ∀ (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[lam] O'],
      (lam : O') ∈ IsLocalRing.maximalIdeal O' →
      ∃ (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
            Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (Jac q M')))
        (T : HeckeAlg →+* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (Jac q M')))
        (G : CuspidalType.GL2 q →* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (Jac q M'))),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : O') (x : TateModule lam (Jac q M')),
            ρ σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] tateGal q M' lam σ x) ∧
        GaloisActionIsAdicContinuous O' ρ ∧
        (∀ (t : HeckeAlg) (a : O') (x : TateModule lam (Jac q M')),
            T t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] tateHecke q M' lam t x) ∧
        (∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ q * M' → T (heckeGen ℓ) = 0) ∧
        (∀ (g : CuspidalType.GL2 q) (a : O') (x : TateModule lam (Jac q M')),
            G g (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] tateGL2 q M' lam g x) := by sorry
