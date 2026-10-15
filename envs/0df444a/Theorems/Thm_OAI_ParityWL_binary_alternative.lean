-- Prove2me | Theorems.Thm_OAI_ParityWL_binary_alternative
-- name    : OAI.ParityWL.binary_alternative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:35:22.547106+00:00
-- url     : https://prove2.me/theorems/d9f80fae-004c-46f6-8687-96a4148ff64a
-- title:
--   Linear alternative over $\mathbb{F}_2$: an unsolvable system $Lz=c$ is certified by a functional
-- statement:
--   Let $E$ and $H$ be vector spaces over the two-element field $\mathbb{F}_2=\mathbb{Z}/2\mathbb{Z}$, of arbitrary (possibly infinite) dimension, let $L:E\to H$ be an $\mathbb{F}_2$-linear map, and let $c\in H$. Then the equation $Lz=c$ has no solution if and only if some linear functional on $H$ vanishes on the image of $L$ and takes the value $1$ at $c$:
--   $$
--   \neg\,\exists\,z\in E:\ Lz=c\quad\iff\quad\exists\,f\in\operatorname{Hom}_{\mathbb{F}_2}(H,\mathbb{F}_2):\ \ f(Lz)=0\ \text{ for all }z\in E\ \text{ and }\ f(c)=1 .
--   $$
--
--   This is a form of the Fredholm alternative over $\mathbb{F}_2$, valid without any rank or finiteness assumption: an inconsistent linear system always has such a certificate $f$, and a certificate rules out every solution. Applied to the constraint map of a projected parity-lift system, it converts inconsistency into a dual object from which the weighted witnesses of the parity reduction are built.
--
--   **Formalization Note** The statement is for additive commutative groups `E`, `H` carrying `Module Bit` structures, where `Bit = ZMod 2`; the functional is an element of `H →ₗ[Bit] Bit`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean#L235-L254

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts

open OAI OAI.ParityWL
open scoped BigOperators
variable {E H : Type} [AddCommGroup E] [Module Bit E] [AddCommGroup H] [Module Bit H]

theorem OAI.ParityWL.binary_alternative (L : E →ₗ[Bit] H) (c : H) :
    (¬ ∃ z, L z = c) ↔
      ∃ f : H →ₗ[Bit] Bit, (∀ z, f (L z) = 0) ∧ f c = 1 := by sorry
