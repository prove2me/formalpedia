-- Prove2me | Theorems.Thm_HILL_PRG_lemma_6_4
-- name    : HILL.PRG.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:24.124154+00:00
-- url     : https://prove2.me/theorems/fa0c5469-1c50-4e10-9358-c47a11155a04
-- title:
--   Lemma 6.4 — entropy gap of ten n squared
-- statement:
--   Fix $n\ge1$ and $k\ge125n^3$. Construct the two finite output laws $\mathcal D$ and $\mathcal E$ from (6.8): $\mathcal D$ begins with a universal hash of the parity bits $X'_j\odot Y'_j$, and $\mathcal E$ replaces that block by independent uniform bits. The remainder of the outputs and their public keys agree. Then
--
--   $$
--   H(\mathcal E)\ge H(\mathcal D)+10n^2.
--   $$
--
--   This is the numerical false-entropy gap behind Theorem 6.2.
--
--   **Formalization Note** The statement assumes $\widetilde D_f(f(x))\le n-1$ for every $n$-bit $x$. The printed proof uses this to get $\Pr[I'<\widetilde D_f(f(X'))]=p_n-1/n$; at a constant function the identity fails. For an asymptotically one-way $f$ the condition eventually holds, which is enough for Theorem 6.2 under the eventual-entropy convention. Equation (6.6) is floored to a bit length. The seed indices are uniform on `Fin n`, repairing the printed bit-block range.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, p. 1387, Lemma 6.4; distribution definitions in proof of Theorem 6.2, p. 1386

import Mathlib
import Definitions.Def_HILL_PRG_Model
import Definitions.Def_HILL_PRG_Constructions

namespace HILL.PRG

/-- Lemma 6.4, p. 1387: the exact entropy gap for the finite product seed. -/
theorem lemma_6_4 (F : FunEns) (n k : ℕ) (hn : 1 ≤ n)
    (hk : 125 * n ^ 3 ≤ k)
    (hD : ∀ x ∈ cube n,
      Dtilde (cube n) (F.f 0 n) (F.f 0 n x) ≤ n - 1)
    (h hp : HashFamily) (hh : h.IsUniversal) (hhp : hp.IsUniversal)
    (hin : h.inLen n = n)
    (hout : h.outLen n = n + Nat.clog 2 (2 * n))
    (hpin : hp.inLen n = k)
    (hpout : hp.outLen n = m64 F (fun _ => k) n) :
    entropyD64 F h hp n k + 10 * (n : ℝ) ^ 2 ≤
      entropyE64 F h hp n k (m64 F (fun _ => k) n) := by sorry

end HILL.PRG
