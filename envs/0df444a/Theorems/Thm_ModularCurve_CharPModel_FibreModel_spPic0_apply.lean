-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPic0_apply
-- name    : ModularCurve.CharPModel.FibreModel.spPic0_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/1e3b39b9-4c2b-5da4-9b1c-0799f4ce28e5
-- title:
--   Specialisation on Pic⁰ computes by divisor pushforward
-- statement:
--   Fix a natural number $N \neq 0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$, a field $k$ of characteristic $\ell$, and a ring homomorphism $\mathrm{red} : A \to k$; let $fm$ be a `FibreModel` for these data (a pair of subrings $B_{\mathrm{fin}}, B_\infty$ of the base change of the level-$N$ modular function field to $\overline{\mathbb{Q}}$, integral over the two affine bases, containing the constants from $A$ and the relevant values of $j$, together with reduction homomorphisms $\pi_{\mathrm{fin}}, \pi_\infty$ into the modular function field over $k$ compatible with $\mathrm{red}$ and with the $q$-expansions mod $\ell$). Assume $\mathrm{red}$ is surjective, and let `dataAll` assign to each divisor $d \mid N$ modular polynomial data, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ annihilating $j_{q^d}$ over $j$; assume the hypothesis `hsep`, that the image of $\Phi$ for $d = N$ in $\mathrm{RatFunc}(k)[Y]$ is separable. Assume further `hpres`, the conjunction: the pushforward $\mathrm{spDiv}$, given by `Finsupp.mapDomain` along the place map `fm.spPlace`, carries degree-zero divisors on the modular curve over $\overline{\mathbb{Q}}$ to degree-zero divisors over $k$, and carries principal degree-zero divisors to principal ones. Then for every degree-zero divisor $D$ (an element of the kernel of the degree homomorphism on the free $\mathbb{Z}$-module on places of $\overline{\mathbb{Q}} \subseteq$ the modular function field), the homomorphism `fm.spPic0` sends the class of $D$ in $\mathrm{Pic}^0$ to the class of $\mathrm{spDiv}(D)$, viewed as a degree-zero divisor over $k$ via the first component of `hpres`.
--
--   This is the computation rule for the specialisation map on degree-zero divisor classes attached to a fibre model of the modular curve: the induced homomorphism on $\mathrm{Pic}^0$ is evaluated by pushing divisors forward along the specialisation of places. It is used in identifying the reduction map modulo $\ell$ with the specialisation homomorphism up to the canonical isomorphism of the two descriptions of $\mathrm{Pic}^0$ of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPic0_apply.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.CharPModel.FibreModel.spPic0_apply (N : ℕ) [NeZero N]
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
    fm.spPic0 hred dataAll hsep (AlgebraicCurve.Pic0.mk D)
      = AlgebraicCurve.Pic0.mk
          ⟨fm.spDiv hred dataAll hsep ↑D, hpres.1 ↑D D.2⟩ := by sorry
