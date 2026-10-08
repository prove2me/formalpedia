-- Prove2me | Theorems.Thm_HILL_PRG_theorem_6_2
-- name    : HILL.PRG.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:27.882977+00:00
-- url     : https://prove2.me/theorems/687d60d6-a4ae-4812-9c3e-fcb263eb7947
-- title:
--   Theorem 6.2 — one-way function gives false entropy
-- statement:
--   Let $F$ be a one-way function on $n$-bit inputs. Let $k_n$ be a polynomial-time integer parameter with $k_n\ge125n^3$ and choose the two universal hash families in (6.2) and (6.7). The finite-seed output $\mathcal D_n$ of (6.8) is polynomial-time evaluable given the integer advice $m_n$. It is computationally indistinguishable from the comparison output $\mathcal E_n$, which is also polynomial-time samplable given that advice, and
--
--   $$
--   H(\mathcal E_n)\ge H(\mathcal D_n)+10n^2
--   $$
--
--   for all sufficiently large $n$. Thus the construction has false entropy $10n^2$ in the paper's mildly nonuniform sense.
--
--   **Formalization Note** The formal statement spells out the comparison law as the witness. The advice is $m_n=\lfloor k_np_n-2k_n^{2/3}\rfloor$, the only use of the real number $p_n$ in the construction. The seed index $I'$ is uniform on `Fin n` rather than the larger printed bit-block set; this leaves a gap between the finite product seed and Definition 3.9's uniform bit seed. The entropy bound is eventual because the printed all-$n$ claim uses a degeneracy bound that follows from one-wayness only eventually. Time–success ratios and weak-preserving reduction claims are not modeled.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, p. 1386, Theorem 6.2 and equations (6.1)–(6.8)

import Mathlib
import Definitions.Def_HILL_PRG_Model
import Definitions.Def_HILL_PRG_Constructions

namespace HILL.PRG

/-- Theorem 6.2, p. 1386: the repaired finite-seed generator has 10n² false entropy. -/
theorem theorem_6_2 (F : FunEns) (hf : ∀ n, F.t n = n) (hOWF : IsOWF F)
    (k : ℕ → ℕ) (hkpt : PTimeParam k)
    (hk : ∀ n, 1 ≤ n → 125 * n ^ 3 ≤ k n)
    (h hp : HashFamily) (hh : h.IsUniversal) (hhp : hp.IsUniversal)
    (hin : ∀ n, 1 ≤ n → h.inLen n = n)
    (hout : ∀ n, 1 ≤ n → h.outLen n = n + Nat.clog 2 (2 * n))
    (hpin : ∀ n, 1 ≤ n → hp.inLen n = k n)
    (hpout : ∀ n, 1 ≤ n → hp.outLen n = m64 F k n) :
    IsFalseEntropy64 F h hp k := by sorry

end HILL.PRG
