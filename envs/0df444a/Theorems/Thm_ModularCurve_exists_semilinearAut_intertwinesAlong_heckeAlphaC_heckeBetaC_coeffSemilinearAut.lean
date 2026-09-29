-- Prove2me | Theorems.Thm_ModularCurve_exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut
-- name    : ModularCurve.exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f92264c9-9fd8-564b-a355-fee7a22df6f8
-- title:
--   Coefficient automorphisms extend to the roof, intertwining both Hecke legs
-- statement:
--   Let $N$ and $\ell$ be non-zero natural numbers, let $k$ be a field, and let $\tau$ be a ring automorphism of $k$. Inside the Laurent series field $k((q))$ one has the level-$N$ modular function field `modularFunctionFieldC k N`, the intermediate field generated over $k$ by $j(q)$ and $j(q^N)$, and the roof `charLDegeneracyRoof k N ℓ`, generated over $k$ by $j(q)$, $j(q^N)$, $j(q^\ell)$ and $j(q^{N\ell})$. The two legs are the $k$-algebra maps $\alpha =$ `heckeAlphaC k N ℓ`, the inclusion of the level-$N$ field into the roof, and $\beta =$ `heckeBetaC k N ℓ`, induced by the substitution $q \mapsto q^{\ell}$ (multiplication by $\ell$ on Laurent exponents). Here `coeffSemilinearAut N τ` is the semilinear automorphism of the level-$N$ field given by the pair consisting of coefficientwise application of $\tau$ to $q$-expansions and $\tau$ itself, an element of the subgroup of $\mathrm{Aut}(F) \times \mathrm{Aut}(k)$ of pairs compatible with the structure map. The assertion is that there exists a semilinear automorphism $g'$ of the roof over $k$ such that for every $x$ in the level-$N$ field $g' \cdot \alpha(x) = \alpha(\tau_* x)$ and $g' \cdot \beta(x) = \beta(\tau_* x)$, where $\tau_*$ denotes `coeffSemilinearAut N τ`. No primality of $\ell$, and no hypothesis on the characteristic or perfection of $k$, is required.
--
--   This is the equivariance of the degeneracy (Hecke) correspondence at index $\ell$ under automorphisms of the coefficient field: the correspondence is cut out by equations with rational coefficients, so a coefficientwise automorphism of the level-$N$ function field lifts to the roof compatibly with both projections. Specialised to the Frobenius of a perfect field of positive characteristic it supplies the Frobenius compatibility used in the Čerednik–Drinfeld-style construction of semistable specialisations and in the verification of the Hecke laws for supersingular level data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] {k : Type*} [Field k] (τ : k ≃+* k) :
    ∃ g' : SemilinearAut k ↥(charLDegeneracyRoof k N ℓ),
      SemilinearAut.IntertwinesAlong (heckeAlphaC k N ℓ).toRingHom (coeffSemilinearAut N τ) g' ∧
      SemilinearAut.IntertwinesAlong (heckeBetaC k N ℓ).toRingHom (coeffSemilinearAut N τ) g' := by sorry
