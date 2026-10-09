-- Prove2me | Theorems.Thm_IntMul_TM_transpose
-- name    : IntMul.TM.transpose
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T02:10:47.466024+00:00
-- url     : https://prove2.me/theorems/8ec1fb82-1287-444e-a229-2eda81fecaaf
-- title:
--   Matrix transposition in time $O(N\log\min(m,k))$ on a multitape Turing machine
-- statement:
--   **Matrix transposition.** There are a single deterministic multitape Turing machine $M$ and a constant $c>0$ with the following property. Let $m,k,\ell\ge1$ and let $A=(a_{ij})$ be an $m\times k$ matrix whose entries are bit strings of length $\ell$. Encode $A$ row by row, with a single $\#$ between entries of a row and $\#\#$ between rows:
--   $$a_{11}\#a_{12}\#\cdots\#a_{1k}\#\#a_{21}\#\cdots\#\#a_{m1}\#\cdots\#a_{mk}.$$
--   On this input of length $N$, the machine halts within $c\,(N+1)(\lceil\log_2\min(m,k)\rceil+1)$ steps and outputs the encoding of the $k\times m$ transpose $A^{\mathsf T}$ in the same format.
--
--   Harvey and van der Hoeven use this to move between the layouts of $d$-dimensional arrays (§2.3), at cost $O(N\log\min(m,k))$.
--
--   **Formalization Note** The hypotheses $m,k,\ell\ge1$ make the input word determine $m$, $k$ and $A$. Machine model: `IntMul_MultitapeModel` with arbitrary inputs from `IntMul_MultitapeWords`.
-- source:
--   A. Bostan, P. Gaudry, É. Schost, Linear recurrences with polynomial coefficients and application to integer factorization and Cartier–Manin operator, SIAM J. Comput. 36 (2007), 1777–1806, Appendix (matrix transposition on a multitape Turing machine); used in Harvey–van der Hoeven, Ann. of Math. 193 (2021), §2.3, p. 11.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_MultitapeWords

namespace IntMul.TM

theorem transpose :
    ∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧
      ∀ (m k ℓ : ℕ) (A : Fin m → Fin k → List Bool), 1 ≤ m → 1 ≤ k → 1 ≤ ℓ → (∀ i j, (A i j).length = ℓ) →
        let enc : (m' k' : ℕ) → (Fin m' → Fin k' → List Bool) → List (Option Bool) :=
          fun m' k' B => List.intercalate [none, none]
            (List.ofFn fun i : Fin m' => joinSep (List.ofFn fun j : Fin k' => bits (B i j)))
        ∃ t : ℕ,
          (t : ℝ) ≤ c * (((enc m k A).length + 1 : ℕ) : ℝ) *
            ((Nat.clog 2 (min m k) + 1 : ℕ) : ℝ) ∧
          M.HaltsWithOutputW (enc m k A) t (enc k m fun j i => A i j) := by sorry

end IntMul.TM
