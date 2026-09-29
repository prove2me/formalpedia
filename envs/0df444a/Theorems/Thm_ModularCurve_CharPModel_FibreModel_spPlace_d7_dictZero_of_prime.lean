-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_prime
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/3f751656-d9ef-5c77-a797-5f1e64b70d4d
-- title:
--   Cusp dictionary for j/j_N^N at spPlace, prime level
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a nonzero natural number $N$ which is prime and squarefree with $\ell \nmid N$; a modular-polynomial datum `data` for $\ell$ (a monic bivariate integral polynomial $\Phi_\ell$ of degree $\psi(\ell)$ vanishing at $(j,j_\ell)$) whose reduction modulo $\ell$ equals $(C(X)^\ell - X)(C(X) - X^\ell)$; a field $k$ of characteristic $\ell$ and a surjective ring homomorphism $\mathrm{red}:A\to k$; integrality of the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from level $N$ to level $N\ell$ over $\overline{\mathbb Q}$; modular-polynomial data $\Phi_d$ for all $d \mid N$, with $\Phi_N$ evaluation-symmetric on Laurent series over $\mathbb Q$ and with separable image in $\mathrm{RatFunc}(k)[X]$; a fibre model `fm` of level $N$ at $(A,\mathrm{red})$, and a cusp chart `cc` for it, asserting that $j_N\,j^{-N}$ lies in the ring at infinity of `fm` and is sent by $\pi_\infty$ to $\tilde j_N \tilde j^{-N}$. Then for every place $w$ of the base-changed full modular function field of level $N$ over $\overline{\mathbb Q}$, every $\tau \in A$, and every witness that $j/j_N^N$ lies in the valuation subring of $w$: if $\mathrm{ord}_w(j_N - a) \le 0$ for all $a \in A$, and the residue of $j/j_N^N$ at $w$ equals the image of $\tau$ in the residue field of $w$, then in the level-$N$ modular function field over $k$ one has $\tilde j/\tilde j_N^{\,N} - \mathrm{red}(\tau) = 0$, or else this element has strictly positive order at the place $(fm.\mathrm{spPlace}\ hred\ dataAll\ hsep)\,w$.
--
--   This is the clause `d7_dictZero` of the place-specialization data, verified for the constructed specialization map `FibreModel.spPlace`: it says that the chart coordinate $j/j_N^N$ at a cusp where $j_N$ has a pole transports residues correctly under specialization to characteristic $\ell$. It is one of the inputs to [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq_of_prime`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq_of_prime), which packages the specialization map together with all its properties at prime level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_prime.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_prime
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
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by sorry
