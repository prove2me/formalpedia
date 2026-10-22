-- Prove2me | Theorems.Thm_LoopTwoGroup_Equiv_lemma_5_7
-- name    : LoopTwoGroup.Equiv.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:49.581331+00:00
-- url     : https://prove2.me/theorems/6ed50c12-db7f-4851-a75c-5bfd24e06615
-- title:
--   Lemma 5.7 — smooth splitting from 𝔤_k to P_k𝔤
-- statement:
--   Let $f:[0,2\pi]\to\mathbb R$ be smooth with $f(0)=0$ and $f(2\pi)=1$. For any real $k$ there is a 2-term $L_\infty$ homomorphism $\psi:\mathfrak g_k\to\mathcal P_k\mathfrak g$ such that
--   $$\psi_0(x)=xf,\qquad \psi_1(c)=(0,c),\qquad
--     \psi_2(x_1,x_2)=\bigl([x_1,x_2](f-f^2),0\bigr).$$
--   These splittings supply a homomorphism in the reverse direction for the equivalence of Theorem 5.1.
--
--   **Formalization Note** Lean represents $f$ on all of $\mathbb R$ and requires smoothness only on $[0,2\pi]$. Its constant extension is used in path values outside that interval.
-- source:
--   Baez–Crans–Stevenson–Schreiber, From Loop Groups to 2-Groups, arXiv:math/0504123v3, p. 31, Lemma 5.7

import Mathlib
import Definitions.Def_LoopTwoGroup_Equiv_Model

namespace LoopTwoGroup.Equiv

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
  [FiniteDimensional ℝ g]

/-- Lemma 5.7, p. 31: the section made from a smooth endpoint interpolation. -/
theorem lemma_5_7 (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Icc 0 (2 * Real.pi)))
    (hf0 : f 0 = 0) (hf1 : f (2 * Real.pi) = 1) :
    ∃ Ψ : LInfHom (gk L k) (Pk L k), PsiComponents L k f Ψ := by sorry

end LoopTwoGroup.Equiv
