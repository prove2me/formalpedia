-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
-- name    : ModularCurve.ComplexPlaceDictionary.exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/d22e71b0-7ac7-59bb-9b98-27956fd4995b
-- title:
--   Hecke compatibility of the Abel–Jacobi period map
-- statement:
--   Fix $N \ge 1$ and a prime $\ell$, and write $\mathbb{C}F_M$ for `laurentBaseChange ℂ (modularFunctionFieldFull M)`, the intermediate field of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise images of the divisor $q$-expansions at level $M$. Let $D$ be a complex place dictionary at level $N$: a $\Gamma_0(N)$-invariant assignment $\tau \mapsto D.\mathrm{pt}\,\tau$ of a place of $\mathbb{C}F_N/\mathbb{C}$ to each point of the upper half plane, together with positive multiplicities $e_\tau$, such that $x \in \mathbb{C}F_N$ lies in the valuation subring at $D.\mathrm{pt}\,\tau$ exactly when the norm of the level-$N$ realisation of $x$ is bounded near $\tau$, and such that for $x \ne 0$ the meromorphic order of that realisation at $\tau$ equals $e_\tau \cdot \operatorname{ord}_{D.\mathrm{pt}\,\tau}(x)$. Assume the ring homomorphisms underlying `heckeAlphaBar ℂ N ℓ` and `heckeBetaBar ℂ N ℓ` are integral (hypotheses $h\alpha$, $h\beta$), and that $\mathbb{C}F_{N\ell}$ has principal divisors, i.e. every nonzero element has a degree-zero divisor recording its orders at all places. Let $c : \mathfrak{H} \to_{\mathrm{f}} \mathbb{Z}$ be finitely supported, with the pushforward divisor $\mathrm{mapDomain}\,D.\mathrm{pt}\,c$ of degree $0$. Then there is a finitely supported $c' : \mathfrak{H} \to_{\mathrm{f}} \mathbb{Z}$ whose pushforward divisor equals `heckeDivBar hα hβ` applied to that of $c$ — that is, the image of $\mathrm{mapDomain}\,D.\mathrm{pt}\,c$ under pullback along `heckeBetaBar ℂ N ℓ` followed by pushforward along `heckeAlphaBar ℂ N ℓ` — and such that the functional $\sum_\tau c'(\tau)\,\cdot\,$`periodAlong N I τ` on weight-two cusp forms for $\Gamma_0(N)$, minus the image of $\sum_\tau c(\tau)\,\cdot\,$`periodAlong N I τ` under the transpose `dualHeckeRep N` of the cusp-form Hecke action at the generator `heckeGen ⟨ℓ, _⟩` of the Hecke algebra, lies in the period lattice `periodLattice N`, the $\mathbb{Z}$-span of the range of `period N`.
--
--   This is the divisor-level form of the Hecke equivariance of the Abel–Jacobi map for $X_0(N)$ over $\mathbb{C}$: integration from $i$ against weight-two cusp forms turns the Hecke correspondence on divisors into the transposed Hecke operator $T_\ell$, up to periods. It is used to construct the Hecke-equivariant comparison between $\mathrm{Pic}^0$ of the modular curve over $\mathbb{C}$ and the quotient of the dual of weight-two cusp forms by the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_HeckeOperatorTotal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ComplexPlaceDictionary.exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (ℓ : ℕ) [Fact ℓ.Prime]
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (hβ : ModularCurve.HeckeBetaBarIntegral ℂ N ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull (N * ℓ)))]
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ c' : UpperHalfPlane →₀ ℤ,
      Finsupp.mapDomain D.pt c' = ModularCurve.heckeDivBar hα hβ (Finsupp.mapDomain D.pt c) ∧
      (c'.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) -
          ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩)
            (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
        ModularCurve.periodLattice N := by sorry
