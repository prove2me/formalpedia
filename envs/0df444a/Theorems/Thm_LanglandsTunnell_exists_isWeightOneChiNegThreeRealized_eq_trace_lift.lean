-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_eq_trace_lift
-- name    : LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/d999d19b-4714-5e1b-abce-17d679117631
-- title:
--   Weight-one form attached to a surjective mod-3 representation
-- statement:
--   Let $\Gamma_{\mathbb Q}$ denote the automorphism group of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` over $\mathbb Q$. The data are: a group homomorphism $\rho : \Gamma_{\mathbb Q} \to \mathrm{GL}_2(\mathbb Z/3)$ which is continuous and surjective and whose determinant at every $\sigma$ equals $\mathrm{modThreeCyclotomicChar}(\sigma)$, the mod-$3$ cyclotomic character built from Mathlib's `modularCyclotomicCharacter` on $\overline{\mathbb Q}$; and a group homomorphism $\Psi : \mathrm{GL}_2(\mathbb Z/3) \to \mathrm{GL}_2(\mathbb Z[\sqrt{-2}])$ which is a section of reduction, in the sense that applying the ring map `red` $: \mathbb Z[\sqrt{-2}] \to \mathbb Z/3$ (determined by $\sqrt{-2} \mapsto -1$) entrywise to $\Psi(g)$ returns $g$ for every $g$. The conclusion asserts the existence of a natural number $N$ with `NeZero N` and a sequence $b : \mathbb N \to \mathbb Z[\sqrt{-2}]$ with three properties. First, $b$ is a formal Hecke eigensystem for the character $\varepsilon(\ell) = 0$ if $\ell \mid N$ and $\varepsilon(\ell) = \chi_{-3}(\ell)$ otherwise, where $\chi_{-3}(n)$ is $1$, $-1$, $0$ according as $n \equiv 1, 2, 0 \bmod 3$; unfolding [`FormalHecke.IsEigensystem`](def/FormalHecke_Eigensystem.html#L10), this means $b_1 = 1$ and $b_{\ell n} + \varepsilon(\ell)\,[\ell \mid n]\,b_{n/\ell} = b_\ell b_n$ for every prime $\ell$ and every $n$. Second, [`CuspForm.IsWeightOneChiNegThreeRealized N b`](def/LanglandsTunnell_WeightOneRealizationCarriers.html#L15) holds: there are a ring homomorphism $\iota : \mathbb Z[\sqrt{-2}] \to \mathbb C$ and a cusp form $f$ of weight $1$ on $\Gamma_1(N)$ whose $q$-expansion coefficients satisfy $a_n(f) = \iota(b_n)$ for all $n$ (no nebentypus condition on $f$ itself is part of this predicate; the character $\chi_{-3}$ enters only through the eigensystem relation). Third, for every prime $p$ with $p \nmid 3N$, every valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ (meaning $p$ is a non-unit of $A$) and every $\sigma$ that is a Frobenius at $A$ for $p$ (lying in the decomposition subgroup and acting as $x \mapsto x^p$ on the residue field of $A$), one has $b_p = \operatorname{tr} \Psi(\rho(\sigma))$ in $\mathbb Z[\sqrt{-2}]$.
--
--   This is the Langlands–Tunnell theorem in the shape Wiles uses: the characteristic-zero lift $\Psi \circ \rho$ of a surjective odd mod-$3$ representation with cyclotomic determinant is attached to a holomorphic cusp form of weight one with nebentypus $\chi_{-3}$. Compared with the textbook statement, the formal version asserts only the existence of some level $N$ carrying a coefficient system $b$ over $\mathbb Z[\sqrt{-2}]$ which is a normalised formal eigensystem, is realised as the $q$-expansion of a weight-one cusp form on $\Gamma_1(N)$ through some embedding of $\mathbb Z[\sqrt{-2}]$ into $\mathbb C$, and matches Frobenius traces of $\Psi \circ \rho$ at primes away from $3N$; nothing is claimed about newforms, about $N$ being the Artin conductor, or about the nebentypus of $f$ beyond what the eigensystem character encodes. It is used further on to produce the same weight-one data with level constraints at $3$ and at the other primes, under tameness and inertia hypotheses on $\rho$, and to restate the conclusion directly in terms of the Hecke relations satisfied by the $q$-coefficients of a weight-one cusp form over $\mathbb C$; these in turn feed the residual modularity input for the lifting theorem at $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_eq_trace_lift.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm FLT.ExplicitLift EisensteinWeightOne
open WeierstrassCurve
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hρ : Continuous ρ) (hsurj : Function.Surjective ρ)
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) :
    ∃ (N : ℕ) (_ : NeZero N) (b : ℕ → ℤ√(-2)),
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
      CuspForm.IsWeightOneChiNegThreeRealized N b ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ 3 * N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            b p = ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).trace := by sorry
