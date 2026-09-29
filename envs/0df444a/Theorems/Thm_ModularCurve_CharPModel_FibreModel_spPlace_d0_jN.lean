-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d0_jN
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/11b9b9f4-9b58-5fdd-8e27-e0338274b345
-- title:
--   Specialisation of a place preserves vanishing of j(q^N)-a
-- statement:
--   Fix a level $N \neq 0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$, a field $k$ of characteristic $\ell$ and a ring homomorphism $\mathrm{red} : A \to k$, and let `fm` be a fibre model for these data, i.e. a pair of subrings $B_{\mathrm{fin}}, B_\infty$ of the base change to $\overline{\mathbb{Q}}$ of the full level-$N$ modular function field (realised inside $\overline{\mathbb{Q}}$-Laurent series), containing the constants from $A$ and the relevant generators $\bar\jmath$, $\bar\jmath_N$ and $\bar\jmath^{-1}$, integral over the respective affine bases, together with ring homomorphisms $\pi_{\mathrm{fin}}, \pi_\infty$ to $\mathrm{modularFunctionFieldC}\ k\ N = k(\,\tilde\jmath, \tilde\jmath_N\,)$ compatible with $\mathrm{red}$ and sending the generators to their characteristic-$\ell$ counterparts. Assume $\mathrm{red}$ is surjective; assume given, for every nonzero divisor $d$ of $N$, modular polynomial data $\Phi_d \in \mathbb{Z}[X][Y]$ (monic, of degree $\psi(d)$, annihilating $j(q^d)$ over $j(q)$); assume the reduction of $\Phi_N$ modulo $\ell$, viewed over $k(X)$, is separable, and that $\Phi_N$ is evaluation-symmetric, i.e. $\Phi_N(x,y) = \Phi_N(y,x)$ for all Laurent series $x, y$ over $\mathbb{Q}$. Then for every place $w$ of the $\overline{\mathbb{Q}}$-base-changed modular function field and every $a \in A$: if $\mathrm{ord}_w(\bar\jmath_N - a) > 0$, where $\bar\jmath_N$ is the image of $j(q^N)$ under the coefficient embedding, then $\mathrm{ord}_{w'}(\tilde\jmath_N - \mathrm{red}(a)) > 0$ for the specialised place $w' = \mathrm{spPlace}(w)$ of $k(\tilde\jmath, \tilde\jmath_N)$. Here $\mathrm{ord}$ is minus the logarithm of the adic valuation attached to the place.
--
--   This is the value dictionary in the finite chart at the second generator $j(q^N)$: it says that the specialisation map on places transports a zero of $\bar\jmath_N - a$ to a zero of $\tilde\jmath_N - \mathrm{red}(a)$, the companion of the corresponding statement for the first generator $j(q)$. It feeds the comparison of places and divisor classes under reduction, being used in the identification of specialised degree-zero divisor classes such as [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq) and in the ramification computations for `spPlace`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.CharPModel.FibreModel.spPlace_d0_jN (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hsym : ModularCurve.EvalSymm (dataAll N (dvd_refl N)).Φ) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩
          - algebraMap k (modularFunctionFieldC k N) (red a)) := by sorry
