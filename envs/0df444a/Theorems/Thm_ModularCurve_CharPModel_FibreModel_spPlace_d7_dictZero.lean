-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/5265b982-8620-5b2c-8e36-4c416d7c3751
-- title:
--   Cusp dictionary in the chart j/j_N^N at poles of j_N
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a nonzero $N$ with $N$ squarefree and $\ell \nmid N$, a datum `data : ModularPolynomialData ℓ` (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ killing the pair $(j, j_\ell)$ of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (X^{\ell}-Y)(X-Y^{\ell}) \pmod \ell$, a field $k$ of characteristic $\ell$, a ring homomorphism $\mathrm{red} : A \to k$ that is surjective, integrality of the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from level $N$ to level $N\ell$ over $\overline{\mathbb Q}$, data $\Phi_d$ for every divisor $d \mid N$ with $\Phi_N$ evaluation-symmetric on Laurent series over $\mathbb Q$ and with separable image in $\mathrm{RatFunc}(k)[Y]$ after reduction mod $\ell$, a fibre model `fm` of level $N$ over $(A,\mathrm{red})$, and a cusp chart `cc` for it, i.e. $\bar j_N\,\bar j^{-N} \in$ `fm.BInf` with `fm.piInf` sending it to $\tilde j_N \tilde j^{-N}$. Here $\bar j$ and $\bar j_N$ are the $q$-expansions $j$ and $j(q^N)$ inside the base-changed modular function field $\overline{\mathbb Q}\cdot F_N$, and $\tilde j =$ `jqModC k`, $\tilde j_N =$ `jqNModC k N` their characteristic-$\ell$ analogues inside `modularFunctionFieldC k N`. The assertion is: for every place $w$ of $\overline{\mathbb Q}\cdot F_N$ over $\overline{\mathbb Q}$, every $\tau \in A$ and every proof that $t' = \bar j / \bar j_N^{\,N}$ lies in the valuation ring of $w$, if $\mathrm{ord}_w(\bar j_N - a) \le 0$ for all $a \in A$ and the residue of $t'$ in the residue field of $w$ equals the image of $\tau$, then either $\tilde j/\tilde j_N^{\,N} - \mathrm{red}(\tau) = 0$ in `modularFunctionFieldC k N`, or $\mathrm{ord}$ of this element at the specialised place $(\textit{fm}.\mathrm{spPlace}\ \mathrm{hred}\ \mathrm{dataAll}\ \mathrm{hsep})\,w$ is strictly positive.
--
--   This is the clause `d7_dictZero` of the place-specialisation package for the constructed map `FibreModel.spPlace`: in the chart at the cusps, where $j_N$ has a pole, a point of the characteristic-zero curve whose $j/j_N^N$-coordinate reduces to $\mathrm{red}(\tau)$ specialises to a point where the corresponding function on the characteristic-$\ell$ curve vanishes. It is used by [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq) when assembling the specialisation of places together with the comparison of divisor class groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
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
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by sorry
