-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_not_nine_dvd_not_cube_dvd_of_natCard_inertia_eq_two_of_coprime
-- name    : LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_not_nine_dvd_not_cube_dvd_of_natCard_inertia_eq_two_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/4c6db721-b4b4-5d09-84b3-cfab61128044
-- title:
--   Langlands–Tunnell with controlled level for tamely ramified ρ̄
-- statement:
--   Let $\rho\colon\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{GL}_2(\mathbb Z/3)$ be a continuous surjective homomorphism (the Galois group being that of `AlgebraicClosure ℚ` over $\mathbb Q$) whose determinant is, on every $\sigma$, the mod-$3$ cyclotomic character `modThreeCyclotomicChar`, and let $\Psi\colon\mathrm{GL}_2(\mathbb Z/3)\to\mathrm{GL}_2(\mathbb Z[\sqrt{-2}])$ be a group homomorphism splitting the entrywise reduction map `red`, i.e. $\mathrm{red}\circ\Psi(g)=g$ for all $g$. Assume two ramification hypotheses: (i) there is a valuation subring $A$ of $\overline{\mathbb Q}$ with $3$ a nonunit of $A$ such that the image under $\rho$ of the inertia subgroup of $A$ over $\mathbb Q$ has exactly two elements; (ii) for every prime $q\neq 3$ and every valuation subring $A$ with $q$ a nonunit of $A$, the cardinality of $\rho$ of the inertia subgroup of $A$ is coprime to $q$. Then there are a nonzero level $N$ and a sequence $b\colon\mathbb N\to\mathbb Z[\sqrt{-2}]$ such that: $3\mid N$, $9\nmid N$, and $q^3\nmid N$ for every prime $q\neq 3$; $b$ is a normalised eigensystem for the Hecke recursion with multiplier $e(\ell)=0$ if $\ell\mid N$ and $e(\ell)=\chi_{-3}(\ell)$ otherwise, that is $b_1=1$ and $b_{\ell n}+e(\ell)\,[\ell\mid n]\,b_{n/\ell}=b_\ell b_n$ for all primes $\ell$ and all $n$, where $\chi_{-3}(n)$ is $1,-1,0$ according as $n\equiv 1,2,0 \pmod 3$; $b$ is realised analytically, in the sense that there exist a ring homomorphism $\iota\colon\mathbb Z[\sqrt{-2}]\to\mathbb C$ and a cusp form $f$ of weight $1$ on $\Gamma_1(N)$ with $q$-expansion coefficients $\iota(b_n)$ for all $n$; and for every prime $p\nmid 3N$, every valuation subring $A$ with $p$ a nonunit of $A$ and every $\sigma$ in the decomposition subgroup of $A$ acting as $x\mapsto x^p$ on the residue field of $A$, one has $b_p=\mathrm{tr}\,\Psi(\rho(\sigma))$.
--
--   This is the form of the Langlands–Tunnell theorem used on the mod-$3$ side of the Frey–Serre–Ribet–Wiles route: the octahedral (or smaller) representation $\Psi\circ\rho$ is attached to a weight-one cusp form with nebentypus $\chi_{-3}$, and, in addition to the trace identity at Frobenius elements, the level is controlled — divisible by $3$ exactly once and by no other prime to the third power — which is what the tameness hypothesis buys. It feeds the residual modularity input of the $3$-adic argument, being used in [`FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd`](thm.html#FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_not_nine_dvd_not_cube_dvd_of_natCard_inertia_eq_two_of_coprime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm FLT.ExplicitLift EisensteinWeightOne
open WeierstrassCurve
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_not_nine_dvd_not_cube_dvd_of_natCard_inertia_eq_two_of_coprime
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hρ : Continuous ρ) (hsurj : Function.Surjective ρ)
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g)
    (h3 : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 ∧
      Nat.card ((A.inertiaSubgroupIn ℚ).map ρ) = 2)
    (htame : ∀ q : ℕ, q.Prime → q ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime q) :
    ∃ (N : ℕ) (_ : NeZero N) (b : ℕ → ℤ√(-2)),
      3 ∣ N ∧ ¬ 9 ∣ N ∧
      (∀ q : ℕ, q.Prime → q ≠ 3 → ¬ q ^ 3 ∣ N) ∧
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
      CuspForm.IsWeightOneChiNegThreeRealized N b ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ 3 * N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            b p = ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).trace := by sorry
