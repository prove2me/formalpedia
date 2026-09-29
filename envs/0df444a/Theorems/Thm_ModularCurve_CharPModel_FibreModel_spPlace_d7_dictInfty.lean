-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d7_dictInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/2058054e-9075-56b3-aadb-d95f7dd3bf8a
-- title:
--   Cusp dictionary at the j-pole for `spPlace`
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$ and a nonzero $N$ with $N$ squarefree and $\ell \nmid N$. Assume given a modular polynomial datum `data` at level $\ell$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ vanishing on $(j,j_\ell)$) satisfying the Kronecker congruence $\Phi \equiv (X^{\ell}-Y)(X-Y^{\ell}) \pmod \ell$, a field $k$ of characteristic $\ell$ and a surjective ring homomorphism $\mathrm{red} : A \to k$, integrality of both level-$\ell$ degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of $\overline{\mathbb{Q}}$-coefficient base changes of the full level-$N$ function field into level $N\ell$, modular polynomial data $\Phi_d$ for every $d \mid N$ with $\Phi_N$ evaluation-symmetric on Laurent series and with separable image in $\mathrm{RatFunc}(k)[Y]$ after reduction mod $\ell$, a fibre model `fm` of level $N$ over $(A,\mathrm{red})$, and a cusp chart `cc` for it, i.e. $\bar j_N \cdot \bar j^{-N}$ lies in the ring at infinity $B_\infty$ of `fm` and is carried by $\pi_\infty$ to $\tilde j_N \cdot \tilde j^{-N}$ over $k$. Then for every place $w$ of the base-changed full level-$N$ function field over $\overline{\mathbb{Q}}$, every $\tau \in A$ and every witness that $t = \bar j_N/\bar j^{N}$ lies in the valuation subring of $w$: if $\mathrm{ord}_w(\bar j - a) \le 0$ for all $a \in A$, and the residue of $t$ at $w$ equals the image of $\tau$ in the residue field of $w$, then in the level-$N$ function field over $k$ either $\tilde j_N/\tilde j^{N} - \mathrm{red}(\tau) = 0$, or its order at the place $(\mathtt{fm.spPlace}\ \mathrm{hred}\ \mathrm{dataAll}\ \mathrm{hsep})\,w$ is strictly positive.
--
--   This is the cusp-chart clause of the place-specialisation package, verified for the specialisation map `fm.spPlace` constructed from a fibre model: it says that the reduction map on places is compatible with the coordinate $j_N/j^N$ on the chart at the pole of $j$, sending a point where that coordinate has residue $\tau$ to a point where its reduction meets $\mathrm{red}(\tau)$. It is used in assembling the specialisation of places and divisor classes, by [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq) and its prime-level variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictInfty.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d7_dictInfty
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
