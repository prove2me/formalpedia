-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_chartCtx_separated_covering
-- name    : ModularCurve.MultCovering.exists_chartCtx_separated_covering
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/58c44899-6d7c-503a-8555-1973f7272226
-- title:
--   A Fricke-separated covering chart context for X₀(p)
-- statement:
--   Let $p\ge 5$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ satisfying `LiesOverPrime p`, i.e. $p$ is a non-unit of $A$; write $k = \mathrm{ResidueField}(A)$ and assume $k$ has characteristic $p$. Then there exists a chart context $\Gamma :$ `ChartCtx p A`, that is: modular polynomial data `data` for $p$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(p)$ annihilating the pair $(j(q), j(q^p))$) together with a proof `hKr` that $\Phi$ satisfies Kronecker's congruence mod $p$; integrality `hα`, `hβ` of the two degeneracy embeddings of the base-changed level-$1$ field into the base-changed level-$p$ field; a place specialisation `P` of $A$ at $p$ in level $1$ over $k$ with its residue map, and a level-one prolongation pair `R` for it; a set $S_1$ of places of $\overline{\mathbb Q}$ in the base-changed function field of level $1\cdot p$; a finset `Wn` of places of the characteristic-$p$ level-one field `modularFunctionFieldC k 1` whose members are exactly the supersingular places `ssPlaces p 1 k`; finiteness of the supersingular $j$-set `ssJSet p k` together with the count of its cardinality as $\lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$; and a `ChartFstSupply` datum for $R$ and $S_1$ — such that moreover the following two properties hold for all places $W$ of the level-$1\cdot p$ base-changed field: first, if $W \in \Gamma.S_1$ then the Fricke translate $w_p \cdot W$ is not in $\Gamma.S_1$; second, if the reduction $\Gamma.P.\mathrm{redFst}\,W$ is fixed by the square of the geometric-level Frobenius operation on places attached to $\Gamma.data$, $\Gamma.hKr$, is affine (both $j$ and $j_N$ lie in its valuation subring) and is not supersingular, then $W \in \Gamma.S_1$ or $w_p \cdot W \in \Gamma.S_1$.
--
--   This is the root existence statement for the multiplicative covering of $X_0(p)$ at $p$: it produces, over a valuation ring of $\overline{\mathbb Q}$ above $p$, all the data on which the two component charts, the annuli and the associated family are built, with the first sheet separated by the Fricke involution and covering the ordinary Frobenius-square-fixed fibre. It is used by [`ModularCurve.MultCovering.nonempty_chartCtx`](thm.html#ModularCurve.MultCovering.nonempty_chartCtx) and by [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_chartCtx_separated_covering.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_chartCtx_separated_covering (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] :
    ∃ Γ : ChartCtx p A,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
        W ∈ Γ.S₁ → frickeInvolutionBar (1 * p) • W ∉ Γ.S₁) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
        frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr
            (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W)) = Γ.P.redFst W →
        IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redFst W) → Γ.P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A) →
        W ∈ Γ.S₁ ∨ frickeInvolutionBar (1 * p) • W ∈ Γ.S₁) := by sorry
