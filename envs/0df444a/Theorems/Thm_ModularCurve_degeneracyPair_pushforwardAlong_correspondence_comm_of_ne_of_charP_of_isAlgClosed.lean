-- Prove2me | Theorems.Thm_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_comm_of_ne_of_charP_of_isAlgClosed
-- name    : ModularCurve.degeneracyPair_pushforwardAlong_correspondence_comm_of_ne_of_charP_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/27d26ecc-6257-52ed-83aa-c9211041ecd7
-- title:
--   Degeneracy maps commute with the ℓ-Hecke correspondence on divisors
-- statement:
--   Fix natural numbers $M, s, \ell, q'$ with $M, s$ nonzero, $s$, $\ell$ and $q'$ prime, $\ell \neq s$, $s \neq q'$, $\ell \neq q'$, and with neither $q'$ nor $s$ dividing $M$, and let $k$ be an algebraically closed field of characteristic $q'$. Assume that the two fields $\mathtt{charLDegeneracyRoof}\,k\,(Ms)\,\ell$ and $\mathtt{charLDegeneracyRoof}\,k\,M\,\ell$ — the intermediate fields of $\mathrm{LaurentSeries}\,k$ generated over $k$ by $\mathtt{jqModC}$ together with the three functions $\mathtt{jqNModC}$ at levels $N$, $\ell$ and $N\ell$, for $N = Ms$ and $N = M$ respectively — have principal divisors, i.e. every nonzero element admits a degree-zero divisor recording its order at each place. Let $\varphi_0, \varphi_1$ be $k$-algebra maps from $\mathtt{modularFunctionFieldC}\,k\,M = k(\mathtt{jqModC}, \mathtt{jqNModC}\,M)$ to $\mathtt{modularFunctionFieldC}\,k\,(Ms)$, both integral, with $\varphi_0$ acting on Laurent series as the identity and $\varphi_1$ acting as $\mathtt{qExpand}\,k\,s$ (multiplication of exponents by $s$). Assume the two Hecke legs at $\ell$, namely the inclusion $\mathtt{heckeAlphaC}$ and the substitution $\mathtt{heckeBetaC}$ into the respective roofs, are integral at level $Ms$ and at level $M$. Then for $i \in \{0,1\}$ and every divisor $D$ of $\mathtt{modularFunctionFieldC}\,k\,(Ms)$, pushforward along $\varphi_i$ commutes with the correspondence "pull back along $\mathtt{heckeAlphaC}$, then push forward along $\mathtt{heckeBetaC}$": the pushforward of the correspondence applied to $D$ equals the level-$M$ correspondence applied to the pushforward of $D$.
--
--   This is the compatibility of the two degeneracy maps between levels $M$ and $Ms$ with the Hecke correspondence $T_\ell$, on divisors of the corresponding function fields, in the stratum where the Hecke prime $\ell$ differs from the level prime $s$ and from the characteristic $q'$. It feeds the construction of Hecke transport on semistable specialisations of two-level data and the computation of degeneracy matrices for special-fibre level data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_comm_of_ne_of_charP_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.degeneracyPair_pushforwardAlong_correspondence_comm_of_ne_of_charP_of_isAlgClosed
    (M s ℓ q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hℓ : ℓ.Prime) [Fact q'.Prime] (hℓs : ℓ ≠ s)
    (hsq' : s ≠ q') (hℓq' : ℓ ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) ℓ)]
      [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M ℓ)]
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x)
      (hα₁ : HeckeAlphaCIntegral k (M * s) ℓ) (hβ₁ : HeckeBetaCIntegral k (M * s) ℓ)
      (hα₀ : HeckeAlphaCIntegral k M ℓ) (hβ₀ : HeckeBetaCIntegral k M ℓ)
      (i : Fin 2) (D : Divisor k ↥(modularFunctionFieldC k (M * s))),
      Divisor.pushforwardAlong (φ i) (hφ i)
          (Divisor.correspondence (heckeAlphaC k (M * s) ℓ) (heckeBetaC k (M * s) ℓ) hα₁ hβ₁ D)
        = Divisor.correspondence (heckeAlphaC k M ℓ) (heckeBetaC k M ℓ) hα₀ hβ₀
            (Divisor.pushforwardAlong (φ i) (hφ i) D) := by sorry
