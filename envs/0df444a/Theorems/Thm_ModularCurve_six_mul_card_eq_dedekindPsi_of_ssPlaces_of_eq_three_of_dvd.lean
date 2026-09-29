-- Prove2me | Theorems.Thm_ModularCurve_six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd
-- name    : ModularCurve.six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/63bd621f-a085-5a4a-8a82-db4569bcc517
-- title:
--   Characteristic-3 supersingular places of X₀(M'): 6|W|=ψ(M')
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number not divisible by $q$, and suppose there is a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ dividing $M'$. Let $\kappa$ be an algebraically closed field of characteristic $q$, and work with the modular function field `modularFunctionFieldC κ M'`, the subfield of the Laurent series field $\kappa((X))$ generated over $\kappa$ by the two series `jqModC κ` and `jqNModC κ M'` (the $q$-expansion of $j$ and its $M'$-fold substitution). A place of this extension is, by definition, a valuation subring of it which contains the image of $\kappa$, is not the whole field, and is a principal ideal ring. Let $W$ be a finite set of such places characterised by the property that a place lies in $W$ exactly when it lies in `ssPlaces q M' κ`, that is, when it is rational, is an affine geometric place in the sense of the predicate `IsAffineGeomPlace`, and its value at the generator `jGeomGen κ M'` belongs to the set `ssJSet q κ` of supersingular $j$-invariants in characteristic $q$. The conclusion is the equality of natural numbers $6\,\lvert W\rvert = \psi(M')$, where $\psi(M')$ is `dedekindPsi M'`, defined as $\sum_{d \mid M',\ d \text{ squarefree}} M'/d$.
--
--   This is the Eichler–Deuring supersingular point count for $X_0(M')$ in characteristic $3$, specialised to an auxiliary level $M'$ divisible by a prime $\ell \equiv 11 \pmod{12}$, for which $X_0(M')$ has no elliptic points, so that the mass formula becomes an exact count: each supersingular place carries automorphism group of order $6$ beyond $\pm 1$ in the relevant normalisation, giving $\lvert W\rvert = \psi(M')/6$. It feeds the genus computations for the function fields attached to $X_0(M')$ and to the auxiliary level-$H$ curves in characteristic $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.six_mul_card_eq_dedekindPsi_of_ssPlaces_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ]
    (W : Finset (Place κ (modularFunctionFieldC κ M'))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' κ) :
    6 * W.card = dedekindPsi M' := by sorry
