-- Prove2me | Theorems.Thm_Nullstellensatz_algebraicSet_radicalIdeal_correspondence
-- name    : Nullstellensatz.algebraicSet_radicalIdeal_correspondence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:03:23.126987+00:00
-- url     : https://prove2.me/theorems/afbc1e7c-6867-4781-8f8d-181970f4f0f7
-- title:
--   Algebraic sets correspond to radical ideals
-- statement:
--   Let $K$ be algebraically closed. The map $J \mapsto \mathrm V(J)$ is an order-reversing bijection from the radical ideals of $K[X_1,\dots,X_n]$ onto the algebraic sets in $K^n$, with inverse $W \mapsto \mathrm I(W)$. Precisely:
--
--   1. $\mathrm V$ maps radical ideals to algebraic sets, injectively and surjectively;
--   2. $J_1 \subseteq J_2 \implies \mathrm V(J_2) \subseteq \mathrm V(J_1)$;
--   3. $\mathrm I(\mathrm V(J)) = J$ for every radical ideal $J$;
--   4. $\mathrm V(\mathrm I(W)) = W$ for every algebraic set $W$.
--
--   This is the dictionary between affine geometry over $K$ and radical ideals.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 5 (order-reversing bijective correspondence between algebraic sets and radical ideals).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem algebraicSet_radicalIdeal_correspondence {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} :
    Set.BijOn (zeroSet (K := K) (n := n)) {J | J.IsRadical} {W | IsAlgebraicSet W} ∧
    (∀ J₁ J₂ : Ideal (MvPolynomial (Fin n) K), J₁ ≤ J₂ → zeroSet J₂ ⊆ zeroSet J₁) ∧
    (∀ J : Ideal (MvPolynomial (Fin n) K), J.IsRadical → vanishingIdeal (zeroSet J) = J) ∧
    (∀ W : Set (Fin n → K), IsAlgebraicSet W → zeroSet (vanishingIdeal W) = W) := by sorry

end Nullstellensatz
