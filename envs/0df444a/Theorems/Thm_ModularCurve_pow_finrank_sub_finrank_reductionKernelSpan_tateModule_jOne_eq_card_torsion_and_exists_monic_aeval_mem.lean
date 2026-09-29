-- Prove2me | Theorems.Thm_ModularCurve_pow_finrank_sub_finrank_reductionKernelSpan_tateModule_jOne_eq_card_torsion_and_exists_monic_aeval_mem
-- name    : ModularCurve.pow_finrank_sub_finrank_reductionKernelSpan_tateModule_jOne_eq_card_torsion_and_exists_monic_aeval_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/c6fa6863-5920-5240-a9bc-b08b02a574fe
-- title:
--   Reduction kernel in TₚJ₁(M): corank and a Tₚ-polynomial
-- statement:
--   Fix $M \ge 1$ and a prime $p$ with $p \nmid M$, and let $K$ be a field of characteristic zero equipped with a $\mathbb{Z}_p$-algebra structure. Let $J_1(M) =$ [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186) be the degree-zero divisor class group $\mathrm{Pic}^0$ of the $q$-expansion function field of $X_1(M)$ over $\overline{\mathbb{Q}}$, carrying the Hecke-algebra module structure [`ModularCurve.heckeModuleOneBar M`](def/ModularCurve_X1HeckeModule.html#L129), and let $T =$ [`TateModule p (ModularCurve.JOne M)`](def/EllipticCurve_TateModule.html#L15) be the group of sequences $x : \mathbb{N} \to J_1(M)$ with $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$. The assertion is that for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $P$, writing $C$ for the $K$-span inside $K \otimes_{\mathbb{Z}_p} T$ of the image of $\{x \in T : \mathrm{red}_P(x_n) = 0 \text{ for all } n\}$ under $x \mapsto 1 \otimes x$, where $\mathrm{red}_P$ is the reduction map [`ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M)`](def/ModularCurve_QExpReductionModL.html#L312) on divisor classes induced by the residue map of $P$: first, $p$ raised to the power $\dim_K (K \otimes_{\mathbb{Z}_p} T) - \dim_K C$ equals the cardinality of the $p$-torsion subgroup $\{y \in \mathrm{Pic}^0$ of the $q$-expansion function field of $X_1(M)$ over the residue field of $P$ $: p \cdot y = 0\}$; and second, there is a monic $Q \in \mathbb{Z}_p[X]$ whose constant coefficient is a unit such that, for every $v \in K \otimes_{\mathbb{Z}_p} T$, the value at $v$ of $Q$ (mapped to $K[X]$) evaluated on the $K$-base change of the endomorphism of $T$ given by the $p$-th Hecke generator [`ModularCurve.heckeGenOne ⟨p, _⟩`](def/ModularCurve_X1HeckeModule.html#L18) under [`ModularCurve.tateHeckeRepOne`](def/ModularCurve_X1HeckeModule.html#L176) lies in $C$.
--
--   This is the Serre–Tate style splitting of the $p$-adic Tate module of $J_1(M)$ at a place above $p \nmid M$: the classes killed by reduction span a subspace whose corank records the $p$-rank of the Jacobian of $X_1(M)$ over the residue field, and, by the Eichler–Shimura congruence, $T_p$ acts on the quotient through a monic polynomial with unit constant term. It is used by [`ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit`](thm.html#ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit) in the analysis of the ordinary part of the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_finrank_sub_finrank_reductionKernelSpan_tateModule_jOne_eq_card_torsion_and_exists_monic_aeval_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.pow_finrank_sub_finrank_reductionKernelSpan_tateModule_jOne_eq_card_torsion_and_exists_monic_aeval_mem
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K] :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      p ^ (Module.finrank K (K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)) -
          Module.finrank K ↥(Submodule.span K
              ((fun x : TateModule p (ModularCurve.JOne M) => (1 : K) ⊗ₜ[ℤ_[p]] x) ''
                {x | ∀ n : ℕ, ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M)
                  ((x : ℕ → ModularCurve.JOne M) n) = 0}))) =
          Nat.card {y : ModularCurve.JOneC M (IsLocalRing.ResidueField P) // p • y = 0} ∧
      ∃ Q : Polynomial ℤ_[p], Q.Monic ∧ IsUnit (Q.coeff 0) ∧
        ∀ v : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M),
          Polynomial.aeval
              ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
                (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).baseChange K)
              (Q.map (algebraMap ℤ_[p] K)) v ∈
            Submodule.span K
              ((fun x : TateModule p (ModularCurve.JOne M) => (1 : K) ⊗ₜ[ℤ_[p]] x) ''
                {x | ∀ n : ℕ, ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M)
                  ((x : ℕ → ModularCurve.JOne M) n) = 0}) := by sorry
