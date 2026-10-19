-- Prove2me | Theorems.Thm_MazurTransfer_PolynomialPowerSubstitutionPresentation_backward_forward
-- name    : MazurTransfer.PolynomialPowerSubstitutionPresentation.backward_forward
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:04:41.563867+00:00
-- url     : https://prove2.me/theorems/f791e98c-0efd-4bb3-b106-02e63ccf5941
-- title:
--   The backward power-substitution map inverts the forward map
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, and put $C=R[T][Y]/(Y^n-T)$. The literal forward map $F:C\to R[X]$ sends $Y$ to $X$ and $T$ to $X^n$, while the backward map $G:R[X]\to C$ sends $X$ to $Y$. Then $$G\circ F=\operatorname{id}_C.$$ This is the inverse identity needed by the specified power-substitution algebra isomorphism and basis used to increase actual order-thirteen finite-map degrees.
-- source:
--   Original backward_forward theorem from MazurTheorem PolynomialPowerSubstitutionPresentation.lean, Apache-2.0, Vas and contributors. The thirteen-line proof body and its two original inline helpers are unchanged. Literal maps are imported from the public Definitions interface. The original and public formal types are compared in the kernel with closed term and universe parameters. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: original presentationEquiv, polynomial power bases and arbitrarily-large actual order-thirteen FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionMaps
open Polynomial MazurTransfer.PolynomialPowerSubstitutionPresentation
universe u

theorem MazurTransfer.PolynomialPowerSubstitutionPresentation.backward_forward (R : Type u) [CommRing R] (n : ℕ) : (backward R n).comp (forward R n) = RingHom.id _  := by sorry
