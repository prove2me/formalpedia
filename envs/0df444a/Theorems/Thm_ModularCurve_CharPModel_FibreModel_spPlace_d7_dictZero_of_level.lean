-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/a03daa8c-0ed8-5a20-82a0-4dcce75199b5
-- title:
--   Cusp dictionary at the j_N-pole in the chart j/j_N^N
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $\ell$ be a prime and $N\ge 1$ with $\ell\nmid N$. Let `data` be a modular-polynomial datum at level $\ell$, i.e. a polynomial $\Phi\in\mathbb Z[x][y]$, monic in $y$ of degree $\psi(\ell)$, with $\Phi(j,j_\ell)=0$ for the $q$-expansions, and assume the Kronecker congruence: modulo $\ell$ one has $\Phi\equiv(x^{\ell}-y)(x-y^{\ell})$. Let $k$ be a field of characteristic $\ell$ and $\mathrm{red}:A\to k$ a surjective ring homomorphism; assume the two degeneracy embeddings $\bar\alpha,\bar\beta$ from level $N$ to level $N\ell$ over $\overline{\mathbb Q}$ are integral. Let there be given, for each divisor $d\mid N$, a modular-polynomial datum $\Phi_d$, with $\Phi_N$ evaluation-symmetric ($\Phi_N(x,y)=\Phi_N(y,x)$ on Laurent series over $\mathbb Q$) and with the image of $\Phi_N$ in $k(x)[y]$ separable. Let `fm` be a fibre model of level $N$ at $(A,\mathrm{red})$ and `cc` a cusp chart for it, so that $\bar j_N\bar j^{-N}$ lies in the ring at infinity and is carried by $\pi_\infty$ to $j_N j^{-N}$ in characteristic $\ell$. Then for every place $w$ of the base-changed modular function field $\overline{\mathbb Q}\cdot\bar F_N$, every $\tau\in A$, and assuming $\bar j/\bar j_N^{\,N}$ lies in the valuation ring of $w$: if $\mathrm{ord}_w(\bar j_N-a)\le 0$ for every $a\in A$, and the residue of $\bar j/\bar j_N^{\,N}$ at $w$ is the image of $\tau$ in the residue field of $w$, then in the characteristic-$\ell$ modular function field $k\cdot F_N$ either $j/j_N^{\,N}-\mathrm{red}(\tau)=0$, or its order at the place $(\mathtt{fm.spPlace}\ \ldots)\,w$ is strictly positive.
--
--   This is the clause `d7_dictZero` of the place-specialization package, verified for the specialization map `FibreModel.spPlace` constructed from a fibre model: at a place where $j_N$ has a pole, the chart $j/j_N^N$ transports residues of $w$ to zeros of the reduced function at the specialized place. It feeds the assembly of the place-specialization structure in [`ModularCurve.CharPModel.exists_fibreModel_cuspChart_placeSpecialization_sp_eq_spPlace_of_one_lt`](thm.html#ModularCurve.CharPModel.exists_fibreModel_cuspChart_placeSpecialization_sp_eq_spPlace_of_one_lt) and [`ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_level
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
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by sorry
