-- Prove2me | Theorems.Thm_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC
-- name    : ModularCurve.exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/90e33b06-c89a-57e1-881d-b13576a9e4c4
-- title:
--   A Fricke involution on supersingular places swapping the Hecke legs
-- statement:
--   Let $\kappa$ be an algebraically closed field of characteristic a prime $p$, and let $L \ge 1$ be an integer with $p \nmid L$. Write $F_L =$ `modularFunctionFieldC κ L` for the intermediate field of $\kappa(\!(q)\!)$ generated over $\kappa$ by $j(q)$ and $j(q^L)$, and let `ssPlaces p L κ` be the set of places $w$ of $F_L$ (valuation subrings of $F_L$ containing $\kappa$, distinct from $F_L$, whose valuation ring is a principal ideal ring) satisfying the predicate `IsSupersingularPlace p L κ`. The assertion is that there is a permutation $P$ of this set of places such that: (i) $P$ is an involution, $P(P(x)) = x$; (ii) for all $x, y$ in the set, the action of the semilinear automorphism `arithFrobC p κ L` (the coefficientwise $p$-power Frobenius of $\kappa$ acting on Laurent series) on places satisfies $\mathrm{Frob} \cdot P(y) = P(x)$ if and only if $\mathrm{Frob} \cdot y = x$; and (iii) for every prime $\ell \ne p$, assuming that the degeneracy roof $R_\ell = \kappa(j(q), j(q^L), j(q^\ell), j(q^{L\ell})) =$ `charLDegeneracyRoof κ L ℓ` has principal divisors, and given proofs $h\alpha, h\beta$ that the two legs $\alpha =$ `heckeAlphaC κ L ℓ` (the inclusion $F_L \hookrightarrow R_\ell$) and $\beta =$ `heckeBetaC κ L ℓ` are integral ring homomorphisms, one has, for all $x, y$ in the set of supersingular places, $$\bigl(\alpha_* \beta^* [P(x)]\bigr)(P(y)) = \bigl(\beta_* \alpha^* [x]\bigr)(y),$$ where `Divisor.correspondence φ ψ hφ hψ` is the pushforward along $\psi$ composed after the pullback along $\varphi$, and $[x]$ denotes the divisor `Finsupp.single x 1`.
--
--   This is the Fricke (full Atkin–Lehner) involution $w_L$ of the level-$L$ modular curve in characteristic $p$, given by $j(q) \leftrightarrow j(q^L)$, restricted to the supersingular places: it is an involution commuting with the arithmetic Frobenius and interchanging the two Hecke correspondences $\alpha_*\beta^*$ and $\beta_*\alpha^*$ coming from the degeneracy roof of level $L\ell$. It is used in the construction of the Cartier anchor for the toric monodromy part of the supersingular Hecke family, [`ModularCurve.exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC`](thm.html#ModularCurve.exists_cartierAnchor_toricMonodromyPart_ssHeckeFamilyC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_perm_ssPlaces_correspondence_heckeBetaC_heckeAlphaC_perm_eq_correspondence_heckeAlphaC_heckeBetaC
    (κ : Type*) [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (L : ℕ) [NeZero L] (hpL : ¬ p ∣ L) :
    ∃ P : Equiv.Perm ↥(ssPlaces p L κ),
      (∀ x : ↥(ssPlaces p L κ), P (P x) = x) ∧
      (∀ y x : ↥(ssPlaces p L κ),
        arithFrobC p κ L • ((P y).1 : Place κ ↥(modularFunctionFieldC κ L)) = (P x).1 ↔
          arithFrobC p κ L • (y.1 : Place κ ↥(modularFunctionFieldC κ L)) = x.1) ∧
      (∀ (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ], ℓ ≠ p →
        ∀ [HasPrincipalDivisors κ ↥(charLDegeneracyRoof κ L ℓ)]
          (hα : (heckeAlphaC κ L ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC κ L ℓ).toRingHom.IsIntegral)
          (y x : ↥(ssPlaces p L κ)),
          Divisor.correspondence (heckeBetaC κ L ℓ) (heckeAlphaC κ L ℓ) hβ hα (Finsupp.single (P x).1 1) (P y).1 =
            Divisor.correspondence (heckeAlphaC κ L ℓ) (heckeBetaC κ L ℓ) hα hβ (Finsupp.single x.1 1) y.1) := by sorry
