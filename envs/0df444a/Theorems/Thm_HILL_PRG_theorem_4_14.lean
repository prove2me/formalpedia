-- Prove2me | Theorems.Thm_HILL_PRG_theorem_4_14
-- name    : HILL.PRG.theorem_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:11.733989+00:00
-- url     : https://prove2.me/theorems/02558ae4-2add-441b-aac3-9776e640fa5a
-- title:
--   Theorem 4.14 — pseudoentropy gives a PRG
-- statement:
--   Let $F$ be a polynomial-time ensemble with $n$-bit inputs and pseudoentropy surplus $s_n$, where $s_n$ is a (real-valued) P-time polynomial parameter. In Construction 4.13, form $k_n$ independent outputs of $F$, hash them with any polynomial-time universal family to $j_n$ bits, and publish the hash key. Then the resulting ensemble is a pseudorandom generator:
--
--   $$
--   g(u,y)=(h_y(F^{k_n}(u)),y),\quad
--   k_n=\left\lceil(2m_n+1)/s_n\right\rceil^3,\quad
--   j_n=\left\lfloor k_n(n+s_n)-2m_n k_n^{2/3}\right\rfloor.
--   $$
--
--   This is the extraction step in the paper's conversion from a one-way function to a PRG.
--
--   **Formalization Note** The statement also permits a fixed polynomially bounded integer advice sequence, shared by $F$ and $g$, as needed for the paper's mildly nonuniform intermediate construction. "P-time" for the real parameter $s_n$ is rendered as $s_n=p_n/q_n$ with natural numbers $p_n,q_n$ whose binary expansions are computable from $1^n$ in polynomial time; together with the polynomial-parameter bounds this covers integer and fractional surpluses such as $s_n=1$ or $s_n=1/n$. The hash family has input length $k_n m_n$ and output length $j_n$ at every $n$, as Construction 4.13 states. Bit lengths use the paper's floor and ceiling. Quantitative weak-preserving reduction claims are outside the qualitative security model.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, p. 1380, Construction 4.13 and Theorem 4.14

import Mathlib
import Definitions.Def_HILL_PRG_Model
import Definitions.Def_HILL_PRG_Constructions

namespace HILL.PRG

/-- Theorem 4.14, p. 1380: Construction 4.13 turns pseudoentropy into a PRG.
The real P-time polynomial parameter `s` is a ratio of two naturals that are
computable in binary in polynomial time from `1ⁿ`; the hash family has the
lengths of Construction 4.13 at every `n`. -/
theorem theorem_4_14 (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : PolyParam s)
    (hsP : ∃ p q : ℕ → ℕ, (∀ n, s n = (p n : ℝ) / (q n : ℝ)) ∧
      PolyTimeComputable (fun w => Nat.bits (p w.length)) ∧
      PolyTimeComputable (fun w => Nat.bits (q w.length)))
    (hf : ∀ n, F.t n = n)
    (hPseudo : IsPseudoentropyGen F a s)
    (h : HashFamily) (hh : h.IsUniversal)
    (hin : ∀ n, h.inLen n = k413 F s n * F.ℓ n)
    (hout : ∀ n, h.outLen n = j413 F s n) :
    IsPRG (construction413 F s h) a := by sorry

end HILL.PRG
