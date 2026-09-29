-- Prove2me | Theorems.Thm_ModularCurve_lead_trace_eq_zero_of_forall_le_ord
-- name    : ModularCurve.lead_trace_eq_zero_of_forall_le_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/9670050c-8032-55ed-adee-f73eeec6014c
-- title:
--   Vanishing of leadₓᵃ of a trace at supersingular places
-- statement:
--   Fix a prime $p$ with $5\le p$ and an algebraically closed field $K$ of characteristic $p$, a positive integer $N$ and a prime $\ell$. Write $F=\mathtt{modularFunctionFieldC}\,K\,N$ for the intermediate field of $\mathrm{Laurent}(K)$ generated over $K$ by $\bar\jmath$ and $\bar\jmath_N$, and $R=\mathtt{charLDegeneracyRoof}\,K\,N\,\ell$ for the intermediate field generated over $K$ by $\bar\jmath$, $\bar\jmath_N$, $\bar\jmath_\ell$ and $\bar\jmath_{N\ell}$; let $\alpha=\mathtt{heckeAlphaC}\,K\,N\,\ell\colon F\to R$ be the inclusion, assumed integral as a ring homomorphism, and regard $R$ as an $F$-algebra along $\alpha$. Let $m$ be a natural number and let $x$ be an element of $\mathtt{SSIndex}\,p\,N\,K$ at $k=2m$, i.e. a place $x$ of $F$ lying in $\mathtt{ssPlaces}\,p\,N\,K$ together with the arithmetic conditions $2\le 2m$, $2\mid 2m$, $\mathtt{placeWidth}\,N\,x\mid m$ and $5\le p$; put $a=\mathtt{poleOrder}\,p\,N\,K\,hp5\,(2m)\,x=\bigl(m\,(\mathtt{jWidth}(x(\bar\jmath))-1)\bigr)/\mathtt{placeWidth}\,N\,x$. Let $S$ be a finite set of places of $R$ such that a place $y$ of $R$ lies in $S$ precisely when its restriction along $\alpha$ equals $x$. Assume the strict trace floor: for all $b\in\mathbb Z$ and all $g\in R$, if $\mathrm{ord}_y g\ge -e_\alpha(y)\,b+1$ for every $y\in S$, where $e_\alpha(y)$ is the ramification index of $y$ over $F$ along $\alpha$, then either $\mathrm{Tr}_{R/F}\,g=0$ or $\mathrm{ord}_x\mathrm{Tr}_{R/F}\,g\ge -b+1$. Finally let $\Theta\in R$ satisfy $\mathrm{ord}_y\Theta\ge -e_\alpha(y)\,a+1$ for every $y\in S$. Then $\mathtt{lead}\,N\,K\,x\,a\,(\mathrm{Tr}_{R/F}\,\Theta)=0$, that is, the value at $x$ of $\pi_x^{\,a}\cdot\mathrm{Tr}_{R/F}\,\Theta$ vanishes, $\pi_x$ being the chosen uniformiser at $x$ with $\mathrm{ord}_x\pi_x=1$.
--
--   This is the lift-independence step at the roof level: an element of the degeneracy roof whose order at every place above a supersingular index place $x$ beats the bound $-e_\alpha(y)a+1$ has trace whose $a$-th leading coefficient at $x$ vanishes, so that the trace contributes nothing to the leading term of the $q$-expansion data at $x$. It is used in the construction of the supersingular Hecke operator, in the proofs of its additivity and its compatibility with scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_lead_trace_eq_zero_of_forall_le_ord.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_ModularCurve_SSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.lead_trace_eq_zero_of_forall_le_ord
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral)
    (m : ℕ) (x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)))
    (S : Finset (Place K ↥(charLDegeneracyRoof K N ℓ)))
    (hSx : ∀ y : Place K ↥(charLDegeneracyRoof K N ℓ), y ∈ S ↔ y.restrictAlong (heckeAlphaC K N ℓ) hα = x.1)
    (hTr : ∀ (a : ℤ) (g : ↥(charLDegeneracyRoof K N ℓ)),
      (∀ y ∈ S, -((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ) * a) + 1 ≤ y.ord g) →
        letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) g = 0 ∨
          -a + 1 ≤ x.1.ord (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) g))
    (Θ : ↥(charLDegeneracyRoof K N ℓ))
    (hΘ : ∀ y ∈ S, -((Place.ramificationIndexAlong (heckeAlphaC K N ℓ) y : ℤ)
        * ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x) + 1 ≤ y.ord Θ) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ);
    ModularCurve.lead N K x.1 (ModularCurve.poleOrder p N K hp5 (2 * (m : ℤ)) x)
        (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) Θ) = 0 := by sorry
