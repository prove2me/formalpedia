-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d0_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/7fc6ba43-43b1-561f-90b5-920f9dd232d3
-- title:
--   Finite-chart value dictionary for j under place specialization
-- statement:
--   Fix a positive integer $N$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$, a field $k$ of characteristic $\ell$, and a ring homomorphism $\mathrm{red} : A \to k$. Let $fm$ be a `FibreModel` for these data: a pair of subrings $B_{\mathrm{fin}}, B_{\infty}$ of the base-changed level-$N$ modular function field $\overline{\mathbb{Q}}\cdot(\text{modularFunctionFieldFull } N)$ inside $\overline{\mathbb{Q}}$-Laurent series, containing the constants from $A$ and containing $\bar\jmath = \mathrm{coeffEmb}\,(jq)$ together with $\bar\jmath_N$, resp. $\bar\jmath^{-1}$, each integral over the corresponding affine base ring, equipped with ring homomorphisms $\pi_{\mathrm{fin}}, \pi_{\infty}$ to $\mathrm{modularFunctionFieldC}\,k\,N = k(jq\mathrm{ModC}\,k, jq_N\mathrm{ModC}\,k\,N)$ matching $\mathrm{red}$ on constants and sending $\bar\jmath, \bar\jmath_N, \bar\jmath^{-1}$ to their characteristic-$\ell$ counterparts. Assume $\mathrm{red}$ is surjective, that modular polynomial data (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ annihilating $jq_d$) is given for every nonzero divisor $d \mid N$, and that the level-$N$ polynomial, reduced mod $\ell$ and viewed over $\mathrm{RatFunc}\,k$, is separable. Then for every place $w$ of the base-changed field over $\overline{\mathbb{Q}}$ and every $a \in A$: if $\mathrm{ord}_w(\bar\jmath - a) > 0$, then $\mathrm{ord}_{\mathrm{sp}(w)}(jq\mathrm{ModC}\,k - \mathrm{red}(a)) > 0$, where $\mathrm{sp}$ is the place specialization map `FibreModel.spPlace` attached to $fm$ and these hypotheses, and $\mathrm{ord}$ denotes minus the logarithm of the adic valuation of the place.
--
--   The hypothesis says that $\bar\jmath$ takes the value $a$ at $w$, the conclusion that the characteristic-$\ell$ $j$-function takes the reduced value $\mathrm{red}(a)$ at the specialized place; this is one of the value dictionaries pinning down the specialization map on the finite chart of the fibre model. It is used in the computations of the specialization of divisors and of degree-zero Picard classes, such as [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq) and [`ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap`](thm.html#ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.CharPModel.FibreModel.spPlace_d0_j (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) (red a)) := by sorry
