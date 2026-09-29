-- Prove2me | Theorems.Thm_LSS_lss_nil_schmidt
-- name    : LSS.lss_nil_schmidt
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T18:08:04.424142+00:00
-- url     : https://prove2.me/theorems/e984cc36-f042-4dba-9c52-10e1338a9d71
-- title:
--   Leng–Sah–Sawhney: Schmidt-type decomposition for nilsequences
-- statement:
--   Let $s\ge 3$. There are constants $c,C>0$ depending only on $s$ such that the following holds. Let $N,T,D\ge 1$ be integers, $M\ge 1$, and for $1\le i\le T$ let $G_i/\Gamma_i$ be a nilmanifold of degree $s$, dimension at most $D$ and complexity at most $M$, and $g_i:\mathbb Z\to G_i$ a polynomial sequence. Put $\kappa=c/((T+1)D)^C$. Then $[N]$ can be partitioned into $L$ arithmetic progressions with positive common differences such that
--   $$L\cdot N^{\kappa}\le 2N\qquad\text{and}\qquad d_{G_i/\Gamma_i}\big(g_i(n)\Gamma_i,\ g_i(n')\Gamma_i\big)\le C\,M^{C D^{C}}\,N^{-\kappa}$$
--   for every $i$ and all $n,n'$ in the same progression.
--
--   This is the Schmidt-type decomposition for nilsequences of Leng, Sah and Sawhney (Lemma 2.1 of arXiv:2402.17995, stated there with $N/L\ge N^{\Omega_s(1/(Td)^{O_s(1)})}/2$ and error $M^{O_s(d^{O_s(1)})}N^{-\Omega_s(1/(Td)^{O_s(1)})}$). Nilmanifolds, complexity, polynomial sequences and the metric $d_{G/\Gamma}$ are as in the definition file `LSSNil`, and partitions into progressions (`APPart`) are as in `LSSInterface`.
-- source:
--   J. Leng, A. Sah, M. Sawhney, Improved bounds for Szemerédi's theorem, arXiv:2402.17995, Lemma 2.1 (Section 2, p. 3)

import Mathlib
import Definitions.Def_LSSInterface
import Definitions.Def_LSSNil

open Finset

namespace LSS

theorem lss_nil_schmidt (s : ℕ) (hs : 3 ≤ s) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N T D : ℕ) (M : ℝ) (G : Fin T → Nilmanifold s)
      (g : ∀ i, ℤ → (G i).Mat), 1 ≤ D → 1 ≤ M → (∀ i, (G i).d ≤ D) →
      (∀ i, (G i).complexity ≤ M) → (∀ i, (G i).IsPoly (g i)) →
      ∃ P : APPart N, (P.L : ℝ) * (N : ℝ) ^ (c / (((T : ℝ) + 1) * D) ^ C) ≤ 2 * N ∧
        ∀ i j, ∀ x ∈ P.piece j, ∀ y ∈ P.piece j,
          (G i).distQ (g i x) (g i y) ≤
            C * M ^ (C * (D : ℝ) ^ C) * (N : ℝ) ^ (-(c / (((T : ℝ) + 1) * D) ^ C)) := by sorry

end LSS
