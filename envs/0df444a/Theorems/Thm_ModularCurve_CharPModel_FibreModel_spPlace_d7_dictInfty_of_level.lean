-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d7_dictInfty_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/e8be170b-d363-58ff-a424-2011dc5996a9
-- title:
--   Cusp dictionary in the chart j_N/j^N at j-poles
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a nonzero natural number $N$ with $\ell \nmid N$; a modular-polynomial datum for $\ell$, i.e. a monic $\Phi_\ell$ in $\mathbb Z[x][y]$ of degree $\psi(\ell)$ in $y$ vanishing on $(j,j_\ell)$, whose coefficientwise reduction modulo $\ell$ equals the product of $x^{\ell}-y$ with $x-y^{\ell}$ (the Kronecker congruence, $x$ denoting the inner variable and $y$ the outer one); a field $k$ of characteristic $\ell$ and a surjective ring homomorphism $\mathrm{red}:A \to k$; the integrality of the two degeneracy maps $\alpha,\beta$ from level $N$ to level $N\ell$ of the $\overline{\mathbb Q}$-base-changed full modular function fields; modular-polynomial data $\Phi_d$ for every divisor $d \mid N$, with $\Phi_N$ satisfying $\Phi_N(u,v)=\Phi_N(v,u)$ for all Laurent series $u,v$ over $\mathbb Q$ and having separable image in $\mathrm{RatFunc}(k)[y]$ after reduction mod $\ell$; a fibre model $fm$ of level $N$ over $(A,\mathrm{red})$ together with a cusp chart $cc$ for it, asserting that $\bar j_N\bar j^{-N}$ lies in $fm.BInf$ and is carried by $fm.piInf$ to $j_{N,k}\,j_k^{-N}$. Then for every place $w$ of $\overline{\mathbb Q}\,\bar F_N$ over $\overline{\mathbb Q}$, every $\tau \in A$, and every proof that $t = \bar j_N/\bar j^{\,N}$ lies in the valuation subring of $w$: if $\mathrm{ord}_w(\bar j - a) \le 0$ for all $a \in A$, and the residue of $t$ at $w$ is the image of $\tau$ in the residue field of $w$, then in $k(j_k,j_{N,k}) =$ `modularFunctionFieldC k N` either $j_{N,k}/j_k^{\,N} - \mathrm{red}(\tau) = 0$, or this element has strictly positive $\mathrm{ord}$ at the place $(fm.\mathrm{spPlace}\ hred\ dataAll\ hsep)\,w$ of $k(j_k,j_{N,k})$.
--
--   This is the cusp-dictionary clause, in the chart $t=j_N/j^N$ at places where $j$ has a pole, for the specialization map on places constructed from a fibre model: it says that the specialized place respects the reduction of the $t$-coordinate of such a point. It is one of the clauses verified when assembling the place-specialization package, and is used by [`ModularCurve.CharPModel.exists_fibreModel_cuspChart_placeSpecialization_sp_eq_spPlace_of_one_lt`](thm.html#ModularCurve.CharPModel.exists_fibreModel_cuspChart_placeSpecialization_sp_eq_spPlace_of_one_lt) and [`ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d7_dictInfty_of_level
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
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
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
      ⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩ / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by sorry
