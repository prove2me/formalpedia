-- Prove2me | Theorems.Thm_MosonyiPetz_schwarz_inequality
-- name    : MosonyiPetz.schwarz_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:57.781057+00:00
-- url     : https://prove2.me/theorems/9a584f86-b5b7-4b2a-b3ca-0d4f404ccb7e
-- title:
--   Schwarz inequality $\tau(A^*A)\ge\tau(A)^*\tau(A)$ for unital 2-positive maps
-- statement:
--   Let $\tau:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ be a linear, 2-positive map between matrix algebras with $\tau(I)=I$. Then for every $A\in\mathcal B(\mathcal H)$
--
--   $$\tau(A^*A)\ \ge\ \tau(A)^*\tau(A)$$
--
--   in the operator order. The paper applies it to $T^*$ and to $\alpha$; it underlies the multiplicative-domain arguments of Lemma 1.
--
--   **Formalization Note** The operator inequality is stated as positive semidefiniteness of $\tau(A^*A)-\tau(A)^*\tau(A)$; 2-positivity is `IsTwoPositive`.
--
--   Differences from the source:
--   - encoding: τ(A*A) ≥ τ(A)*τ(A) → (τ (Aᴴ * A) - (τ A)ᴴ * τ A).PosSemidef; reason: Loewner order written as positive semidefiniteness of the difference; same statement
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §2, p.3, unnumbered

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)

namespace MosonyiPetz

/-- **Schwarz inequality for unital 2-positive maps.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §2, p.3, unnumbered: "It is well-known that a 2-positive unit-preserving mapping τ satisfies
the Schwarz inequality τ(A*A) ≥ τ(A)*τ(A)."

For every `ℂ`-linear 2-positive `τ : Matrix H H ℂ → Matrix K K ℂ` with `τ 1 = 1` and every
`A`, the matrix `τ (Aᴴ * A) - (τ A)ᴴ * τ A` is positive semidefinite.

**Formalization Note.** The operator order `X ≥ Y` is written as `(X - Y).PosSemidef`. -/
theorem schwarz_inequality {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (τ : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hτ : IsTwoPositive τ) (h1 : τ 1 = 1)
    (A : Matrix H H ℂ) :
    (τ (Aᴴ * A) - (τ A)ᴴ * τ A).PosSemidef := by sorry

end MosonyiPetz
