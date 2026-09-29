-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPic0_compat
-- name    : ModularCurve.CharPModel.FibreModel.spPic0_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/7b96a3d3-9c59-5c89-b918-a82b7c0d62a4
-- title:
--   Specialisation on Pic⁰ is induced by pushforward of divisors
-- statement:
--   Fix a natural number $N \neq 0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$, a field $k$ of characteristic $\ell$ and a ring homomorphism $\mathrm{red} \colon A \to k$ which is assumed surjective, together with a fibre model `fm` of level $N$ for these data, i.e. an instance of the structure `FibreModel` consisting of two subrings $B_{\mathrm{fin}}, B_{\infty}$ of the base change to $\overline{\mathbb{Q}}$ of the full level-$N$ modular function field, containing the constants from $A$ and the relevant values of $\bar{j}$, $\bar{j}_N$ and $\bar{j}^{-1}$, integral over the corresponding affine bases, and two ring homomorphisms $\pi_{\mathrm{fin}}, \pi_{\infty}$ to `modularFunctionFieldC k N` reducing the constants via $\mathrm{red}$ and sending $\bar{j}, \bar{j}_N$ to their mod-$\ell$ analogues. Fix further a family `dataAll` assigning to every nonzero divisor $d$ of $N$ a `ModularPolynomialData d` (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ annihilating $j_d$ over $j$), and a hypothesis `hsep` that the reduction of $\Phi$ for $d = N$ to $k$, viewed in $\mathrm{RatFunc}(k)[Y]$, is separable. Assume `hpres`: the pushforward $\mathrm{spDiv} =$ `Finsupp.mapDomain (fm.spPlace …)` along the specialisation of places carries degree-zero divisors of the $\overline{\mathbb{Q}}$-curve to degree-zero divisors of the $k$-curve, and carries degree-zero principal divisors to principal divisors. The conclusion: for every degree-zero divisor $D$ on `modularFunctionFieldBar N` there is a degree-zero divisor $D'$ on `modularFunctionFieldC k N` whose underlying divisor equals $\mathrm{spDiv}(D)$ and such that `fm.spPic0` applied to the class of $D$ in $\mathrm{Pic}^0$ equals the class of $D'$.
--
--   This is the compatibility of the specialisation homomorphism on degree-zero divisor classes with the pushforward of divisors along the specialisation of places: the square formed by the two class maps and the two specialisation maps commutes, and the witness $D'$ is exactly the pushforward of $D$. It is the computation rule used whenever a class in $\mathrm{Pic}^0$ of the characteristic-$\ell$ model must be exhibited by an explicit divisor, and it is invoked in the existence results for fibre models with prescribed place specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPic0_compat.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.CharPModel.FibreModel.spPic0_compat (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hpres : fm.SpDivPreservesPrincipal hred dataAll hsep) :
    ∀ D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := ModularCurve.modularFunctionFieldBar N),
    ∃ D' : AlgebraicCurve.Divisor.degZero (K := k)
      (F := ModularCurve.modularFunctionFieldC k N),
      (D' : AlgebraicCurve.Divisor k (ModularCurve.modularFunctionFieldC k N))
          = fm.spDiv hred dataAll hsep ↑D ∧
        fm.spPic0 hred dataAll hsep (AlgebraicCurve.Pic0.mk D) = AlgebraicCurve.Pic0.mk D' := by sorry
