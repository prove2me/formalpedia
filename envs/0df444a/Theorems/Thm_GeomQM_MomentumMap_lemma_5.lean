-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_lemma_5
-- name    : GeomQM.MomentumMap.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:32.072114+00:00
-- url     : https://prove2.me/theorems/f29cdaa0-0d89-402a-ba74-c9b9d5bd79fb
-- title:
--   Lemma 5, p. 12 — f_A(ψ) = ½⟨ψ|Aψ⟩ is real for all ψ iff A is Hermitian
-- statement:
--   Let $A$ be any complex $n\times n$ matrix (an element of $\mathfrak{gl}(n,\mathbb C)$), and define the quadratic function $f_A:\mathbb C^n\to\mathbb C$ by $f_A(\psi)=\tfrac12\langle\psi|A\psi\rangle$. Then
--
--   $$\big(\forall\psi\in\mathbb C^n:\ \operatorname{Im} f_A(\psi)=0\big)\iff A=A^\dagger .$$
--
--   This is what allows a Hermitian observable $A$ to be represented by the real quadratic function $f_A$ on the Hilbert space, the representation used in Proposition 5.
--
--   **Formalization Note** The statement is on the complex value $f_A(\psi)$; $A$ is not assumed Hermitian.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 12, Lemma 5

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem lemma_5 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∀ ψ : Fin n → ℂ, (quadFnC A ψ).im = 0) ↔ A.IsHermitian := by sorry
end GeomQM.MomentumMap
