-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_prime
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/20f9af26-9f66-5793-8471-f7784bb2b6a9
-- title:
--   Cusp-zero dictionary, t-small branch, prime level
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, natural numbers $\ell$, $N$ with $\ell$ prime and $N \neq 0$, and assume $N$ is prime, $N$ is squarefree and $\ell \nmid N$. Fix a modular-polynomial packet `data` for $\ell$ (a bivariate integer polynomial $\Phi$, monic, of degree $\psi(\ell)$, annihilating the pair $(j, j_\ell)$ of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (Y^{\ell} - X)(Y - X^{\ell}) \pmod{\ell}$, a field $k$ of characteristic $\ell$ and a ring homomorphism $\mathrm{red} : A \to k$, assumed surjective; assume the two Hecke degeneracy embeddings $\bar\alpha, \bar\beta$ from the level-$N$ to the level-$N\ell$ base-changed Laurent function field are integral. Fix packets $\Phi_d$ for all divisors $d \mid N$ such that $\Phi_N$ is evaluation-symmetric and such that the image of $\Phi_N$ in $\mathrm{RatFunc}\,k[Y]$, obtained by reducing coefficients into $k$, is separable. Fix a fibre model `fm` of level $N$ over $A$ with reduction $\mathrm{red}$ — a pair of subrings $B_{\mathrm{fin}}, B_{\mathrm{inf}}$ of $\overline{\mathbb{Q}}(X_0(N))\subseteq \overline{\mathbb{Q}}((q))$ containing the constants from $A$ and $\bar\jmath, \bar\jmath_N$ respectively $\bar\jmath^{-1}$, integral over the corresponding affine base rings, together with ring homomorphisms $\pi_{\mathrm{fin}}, \pi_{\mathrm{inf}}$ onto $k(\tilde\jmath, \tilde\jmath_N) = k\big(\{jqModC, jqNModC\}\big)$ compatible with constants and with $\bar\jmath \mapsto \tilde\jmath$, $\bar\jmath_N \mapsto \tilde\jmath_N$ — and assume the cusp chart property: $\bar\jmath_N\,\bar\jmath^{-N} \in B_{\mathrm{inf}}$ with $\pi_{\mathrm{inf}}$-image $\tilde\jmath_N\,\tilde\jmath^{-N}$. Then, for every place $w$ of $\overline{\mathbb{Q}}(X_0(N))$ over $\overline{\mathbb{Q}}$ (a proper valuation subring containing $\overline{\mathbb{Q}}$ whose ideals are principal) and every $\tau \in A$ such that $\bar\jmath/\bar\jmath_N^{\,N}$ lies in the valuation subring of $w$: if $w.\mathrm{ord}(\bar\jmath_N - a) \le 0$ for all $a \in A$, if the residue of $\bar\jmath/\bar\jmath_N^{\,N}$ at $w$ is the image of $\tau$ in the residue field of $w$, and if $\bar\jmath_N/\bar\jmath^{\,N} - a$ is a nonunit of the valuation subring of $w$ for some $a$ in the maximal ideal of $A$, then the element $\tilde\jmath/\tilde\jmath_N^{\,N} - \mathrm{red}(\tau)$ of $k(\tilde\jmath, \tilde\jmath_N)$ is either zero or has strictly positive order at the specialised place $\mathrm{sp}_{\mathrm{fm}}(w)$.
--
--   This is the branch of the unit dictionary at the cusp $0$ in which the Tate-like parameter $t = j_N/j^{\,N}$ is congruent to an element of the maximal ideal of $A$: the conclusion transports the vanishing of $j/j_N^{\,N} - \tau$ from the characteristic-zero place $w$ to the specialised place in characteristic $\ell$. It feeds, together with the complementary branches, into [`ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_prime`](thm.html#ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_prime), and uses the dichotomy [`ModularCurve.forall_ord_jBar_sub_le_zero_or_exists_ord_pos`](thm.html#ModularCurve.forall_ord_jBar_sub_le_zero_or_exists_ord_pos) for the behaviour of $\bar\jmath$ at $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_prime.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

set_option autoImplicit false

noncomputable section

theorem ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small_of_prime
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hN : N.Prime)
    (hsq : Squarefree N) (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
    (∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
          ∈ w.toValuationSubring.nonunits) →
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by sorry
