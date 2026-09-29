-- Prove2me | Theorems.Thm_ModularCurve_finrank_span_toricMonodromyPart_eq_finrank_of_not_exists_hasLowerLevelTorsion
-- name    : ModularCurve.finrank_span_toricMonodromyPart_eq_finrank_of_not_exists_hasLowerLevelTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/3687b62a-9fb2-5880-9cdb-a9d63a2d6552
-- title:
--   𝔪-torsion is entirely toric at level Nq'q
-- statement:
--   Let $p$ be a prime, let $N,q,q'$ be natural numbers with $q$ and $q'$ prime, $q\nmid N$, $q'\neq q$ and $q\neq p$, and assume $Nq'$ and $q$ are nonzero. Work in the Hecke algebra $\mathbb{T}=$ `HeckeAlg` $=\mathbb{Z}[T_\ell:\ell\text{ prime}]$ (the polynomial ring on the primes), acting on $J=$ `JZero` $M$, the degree-zero divisor class group of the modular function field of level $M$ over $\overline{\mathbb{Q}}$, via the Hecke module structure `heckeModuleBar`. Let $\mathfrak m\subset\mathbb{T}$ be a maximal ideal with $p\in\mathfrak m$ which is not eventually Eisenstein, i.e. there is no finite set $S$ of primes with $T_\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$. Let $A_2$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A_2$, and let $I_2=A_2.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$ be the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of its inertia subgroup; assume $I_2$ fixes pointwise the $\mathfrak m$-torsion $J[\mathfrak m]=\{x: \mathfrak m\cdot x=0\}$ of $J=$ `JZero` $(Nq'q)$. Assume furthermore that there is no finite set $S$ of primes, all dividing $Nqq'$, for which `JZero` $(Nq')$ has lower-level torsion at $S$, that is, a nonzero $y$ annihilated by every integer lying in $\mathfrak m$ and by every $T_\ell - b$ ($\ell\notin S$, $b\in\mathbb{Z}$) lying in $\mathfrak m$. Then the $\mathbb{T}/\mathfrak m$-span inside $J[\mathfrak m]$ of those of its elements lying in the toric monodromy part `toricMonodromyPart` $q\,I_2$ — the $\mathbb{T}$-span of the differences $\sigma\bullet x-x$ with $\sigma\in I_2$ and $x$ killed by some positive integer coprime to $q$ — has the same $\mathbb{T}/\mathfrak m$-dimension as $J[\mathfrak m]$ itself.
--
--   This is the modular-side multiplicity statement used in Ribet's level-lowering argument: in the absence of lower-level $\mathfrak m$-torsion on $J_0(Nq')$, the whole of $J_0(Nq'q)[\mathfrak m]$ sits in the $q$-toric part of the monodromy at $q$, so no dimension is lost on passing to the toric part. It feeds the existence statement [`ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero`](thm.html#ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_span_toricMonodromyPart_eq_finrank_of_not_exists_hasLowerLevelTorsion.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.finrank_span_toricMonodromyPart_eq_finrank_of_not_exists_hasLowerLevelTorsion
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (hqp : q ≠ p)
    [NeZero (N * q')] [NeZero q]
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪) (heis : ¬ IsEventuallyEisenstein 𝔪)
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)
    (hunrJ : letI := heckeModuleBar (N * q' * q)
      ∀ σ ∈ A₂.inertiaSubgroupIn ℚ,
        ∀ x ∈ heckeTorsion (JZero (N * q' * q)) 𝔪, σ • x = x) :
    letI := heckeModuleBar (N * q')
    letI := heckeModuleBar (N * q' * q)
    (¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q'))) →
        Module.finrank (HeckeAlg ⧸ 𝔪)
            ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
              ((Subtype.val : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) → JZero (N * q' * q)) ⁻¹'
                (toricMonodromyPart (J := JZero (N * q' * q)) q (A₂.inertiaSubgroupIn ℚ) : Set (JZero (N * q' * q)))))
          = Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) := by sorry
