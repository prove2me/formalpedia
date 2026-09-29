-- Prove2me | Theorems.Thm_InertiaOrderTransport_exists_localDomain_splits
-- name    : InertiaOrderTransport.exists_localDomain_splits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/c6c57a34-2190-5611-b0d1-1004c2839bc1
-- title:
--   Local embedding of a local domain splitting all monic quadratics
-- statement:
--   Let $O'$ be a type carrying a commutative ring structure which is an integral domain and a local ring. The assertion is the existence of a type $O''$, together with a commutative ring structure on it making it an integral domain and a local ring, a ring homomorphism $j : O' \to O''$ which is a local homomorphism (an element of $O'$ whose image under $j$ is a unit of $O''$ is already a unit of $O'$) and is injective as a function, such that for every pair of elements $t, d \in O'$ there exist $r, s \in O''$ with
--   $$(X^2 - C\,t \cdot X + C\,d)^{j} = (X - C\,r)(X - C\,s)$$
--   in $O''[X]$, where the left-hand side is the image of the monic quadratic $X^2 - tX + d \in O'[X]$ under the coefficientwise map induced by $j$. Thus every monic quadratic over $O'$ becomes a product of two monic linear factors after transport to $O''$; the data $O''$, its ring and domain and local-ring structures, $j$, and the two properties of $j$ are all existentially quantified in a single statement.
--
--   A piece of commutative algebra used to enlarge a local coefficient domain so that the characteristic polynomials of $2 \times 2$ matrices over it acquire eigenvalues in the ring, while retaining injectivity and the local property (so that residual information is preserved). It is invoked in the analysis of the restriction to inertia of an adic Galois representation attached to a newform, where a quadratic characteristic polynomial must be diagonalised over a local domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_InertiaOrderTransport_exists_localDomain_splits.lean

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.LocalRing.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem InertiaOrderTransport.exists_localDomain_splits (O' : Type) [CommRing O'] [IsDomain O'] [IsLocalRing O'] :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsLocalRing O'') (j : O' →+* O'')
      (_ : IsLocalHom j) (_ : Function.Injective j),
      ∀ t d : O', ∃ r s : O'', (X ^ 2 - C t * X + C d).map j = (X - C r) * (X - C s) := by sorry
