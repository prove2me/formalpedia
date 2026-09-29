-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN_pole
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d0_jN_pole
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/45534d79-e286-53e3-856b-0a5b13a9ccdb
-- title:
--   Poles of jmath̃_N at places where jmath̄_N has no value in A
-- statement:
--   Let $N$ be a positive integer, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $\ell$ a prime, $k$ a field of characteristic $\ell$, and $\mathrm{red} : A \to k$ a ring homomorphism, assumed surjective. Let `fm` be a fibre model for these data, i.e. subrings $B_{\mathrm{fin}}, B_{\infty}$ of the base-changed field $\overline{\mathbb{Q}} \cdot F_N$ (where $F_N$ is `modularFunctionFieldFull N` inside $\overline{\mathbb{Q}}((q))$) containing the constants from $A$, with $\bar\jmath$ and $\bar\jmath_N$ in $B_{\mathrm{fin}}$ and $\bar\jmath^{-1}$ in $B_{\infty}$, integral over the respective affine bases, together with reduction homomorphisms $\pi_{\mathrm{fin}}, \pi_{\infty}$ to `modularFunctionFieldC k N` $= k(\tilde\jmath, \tilde\jmath_N)$ inducing $\mathrm{red}$ on constants and sending $\bar\jmath \mapsto \tilde\jmath$, $\bar\jmath_N \mapsto \tilde\jmath_N$. Let `dataAll` assign to each divisor $d$ of $N$ a modular polynomial datum (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ with $\Phi(\jmath_d, \cdot)$ annihilating the relevant $q$-expansion), suppose the reduction of $\Phi_N$ over $k$, viewed over $k(X)$, is separable, and suppose $\Phi_N$ satisfies evaluation symmetry: $\Phi(x,y) = \Phi(y,x)$ for all Laurent series $x, y$ over $\mathbb{Q}$. The conclusion: for every place $w$ of $\overline{\mathbb{Q}} \cdot F_N$ over $\overline{\mathbb{Q}}$ (a proper valuation subring containing the constants and a principal ideal ring), if $\mathrm{ord}_w(\bar\jmath_N - a) \le 0$ for every $a \in A$, where $\bar\jmath_N$ is the base change of $\jmath(q^N)$, then $\mathrm{ord}_{\mathrm{sp}(w)}(\tilde\jmath_N) < 0$, $\mathrm{sp}$ being the specialisation of places attached to `fm`, `hred`, `dataAll` and the separability hypothesis.
--
--   This is one entry of the dictionary comparing a place $w$ of the level-$N$ modular function field in characteristic zero with its specialisation in characteristic $\ell$: a place giving the second generator $\bar\jmath_N$ no value in $A$ specialises to a place at which the reduced $\tilde\jmath_N$ has a pole. It feeds the comparison of places and divisor classes under specialisation, notably the results producing a place whose specialised degree-zero class matches a prescribed one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN_pole.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.CharPModel.FibreModel.spPlace_d0_jN_pole (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hsym : ModularCurve.EvalSymm (dataAll N (dvd_refl N)).Φ) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    ((fm.spPlace hred dataAll hsep) w).ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k
        N) < 0 := by sorry
