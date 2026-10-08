-- Prove2me | Theorems.Thm_HILL_PRG_lemma_4_8
-- name    : HILL.PRG.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:05.746012+00:00
-- url     : https://prove2.me/theorems/0d655459-ea71-432d-b377-a9a49c03a0ce
-- title:
--   Lemma 4.8 — leftover hash lemma
-- statement:
--   Let $D$ be a probability distribution on $n$-bit strings with order-two Rényi entropy at least $m$. Let $e>0$ be an integer with $2e\le m$, and let $h_y$ be any polynomial-time pairwise-independent universal hash family from $n$ bits to $m-2e$ bits, with a uniformly random $k$-bit key $Y$. If $X$ has law $D$ and $Z$ is independent and uniform on $m-2e$ bits, then
--
--   $$
--   L_1((h_Y(X),Y),(Z,Y))\le 2^{-(e+1)}.
--   $$
--
--   This is the statistical extraction estimate used when the paper turns entropy into output bits.
--
--   **Formalization Note** Universal hashing uses the exact pairwise-independence identity of Definition 4.6, not a collision-only bound. The finite source law is explicitly nonnegative and normalized. The theorem has no computational hardness premise.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, p. 1378, Lemma 4.8

import Mathlib
import Definitions.Def_HILL_PRG_Model
import Definitions.Def_HILL_PRG_Constructions

namespace HILL.PRG

/-- Lemma 4.8, p. 1378: leftover hashing at Rényi entropy m. -/
theorem lemma_4_8 (n m e kl : ℕ) (he : 0 < e) (hme : 2 * e ≤ m)
    (D : Bits → ℝ) (hD : IsProbOn (cube n) D)
    (hH : (m : ℝ) ≤ renyiOn (cube n) D)
    (h : HashFamily) (hh : h.IsUniversal)
    (hin : h.inLen n = n) (hout : h.outLen n = m - 2 * e)
    (hkey : h.keyLen n = kl) :
    statDistOn (cube (m - 2 * e) ×ˢ cube kl)
      (hashJoint D h n) (hashUniform h n) ≤
      (2 : ℝ) ^ (-((e : ℝ) + 1)) := by sorry

end HILL.PRG
