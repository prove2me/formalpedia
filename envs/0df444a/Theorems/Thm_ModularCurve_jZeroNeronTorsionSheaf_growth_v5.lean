-- Prove2me | Theorems.Thm_ModularCurve_jZeroNeronTorsionSheaf_growth_v5
-- name    : ModularCurve.jZeroNeronTorsionSheaf_growth_v5
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/2884a14f-1337-5e2d-9499-032bcc6d5231
-- title:
--   Common linear growth of δ(m) and trivial-step counts
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, let `hcomm` assert that the Hecke operators `heckeOperatorBar p` commute pairwise on $J =$ `JZero p`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the base-changed modular function field of level $p$ over $\bar{\mathbb Q}$, and let $A$ be a valuation subring of $\bar{\mathbb Q}$ with $p$ in its nonunits (`A.LiesOverPrime p`). Let $S$ be a primary Néron torsion-sheaf datum `JZeroNeronPrimaryTorsionSheaf p q A hA`, consisting of a core, finite-flat models and pinned invariants. Throughout, $J$ carries the `HeckeAlg`-module structure `heckeModuleBar p`, and for each $m$ one writes `eisensteinPrimaryTorsionBar p q m` for the intersection of the kernel of multiplication by $q^m$ on $J$ with the supremum over $k$ of the `HeckeAlg`-torsion submodules killed by $(\mathrm{eisensteinMaximalIdeal}\,p\,q)^k$. Assume given, for every $m$, an action $\Phi_m$ of $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ on that subgroup by additive automorphisms with open kernel, agreeing with the natural Galois action on $J$ after inclusion (`hΦ`), together with an admissible chain $c_m$ for $\Phi_m$ at $q$: a monotone chain of subgroups from $\bot$ to $\top$ with all successive quotients of cardinality $q$, each step tagged `true` or `false` and accordingly trivial ($\Phi_m(\sigma)x - x$ lies in the previous step) or cyclotomic ($\Phi_m(\sigma)x - a\,x$ lies in the previous step whenever $\sigma\zeta = \zeta^a$ for a primitive $q$-th root of unity $\zeta$). Then there exist $g \in \mathbb N$ and $C \in \mathbb Z$ such that for all $m$ the invariant $\delta$ pinned by $S$ at level $m$ satisfies $\delta(m) \le mg + C$, while $mg \le \mathrm{filtAlpha}(c_m) + C$, where $\mathrm{filtAlpha}(c_m)$ is the number of steps of $c_m$ tagged `true`.
--
--   This is the numerical engine behind Mazur's comparison of the toric defect at $p$ of the Eisenstein-primary $q^m$-torsion of $J_0(p)$ with the number of trivial (as opposed to cyclotomic) constituents in an admissible filtration of that torsion: both grow at one common linear rate $g$, up to a single additive constant. It is used in the construction of bounded admissible chains for the Kummer rows of $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jZeroNeronTorsionSheaf_growth_v5.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve MazurAdmissible AlgebraicGeometry AlgebraicGeometry.Scheme

theorem ModularCurve.jZeroNeronTorsionSheaf_growth_v5 (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionSheaf p q A hA)
    (Φ : ∀ m : ℕ,
      letI := heckeModuleBar p
      OpenAction ↥(eisensteinPrimaryTorsionBar p q m))
    (hΦ : ∀ m : ℕ,
      letI := heckeModuleBar p
      ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
        (x : ↥(eisensteinPrimaryTorsionBar p q m)),
        ((Φ m).φ σ x : JZero p) = σ • (x : JZero p))
    (c : ∀ m : ℕ,
      letI := heckeModuleBar p
      AdmissibleChain q (Φ m)) :
    ∃ g : ℕ, ∃ C : ℤ, ∀ m : ℕ,
      letI := heckeModuleBar p
      ((S.invPins.inv m).δ : ℤ) ≤ (m : ℤ) * (g : ℤ) + C ∧
        (m : ℤ) * (g : ℤ) ≤ (filtAlpha (c m) : ℤ) + C := by sorry
