-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_2_4
-- name    : MildHamilton.Main.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:45.244905+00:00
-- url     : https://prove2.me/theorems/4ddd3c85-2dfa-4007-84fa-11160f44762a
-- title:
--   Lemma 2.4, p. 4 — sampling columns preserves the operator norm up to $\sqrt q$
-- statement:
--   Let $F\in\mathbb R^{r\times s}$ with $r,s\ge1$, with columns $f_1,\dots,f_s$, and set $c=\max_{j\in[s]}\|f_j\|_2$. Let $0\le k\le s$, let $I$ be a uniformly random $k$-subset of $[s]$, put $q=k/s$, and let $F_I$ be the submatrix of the columns indexed by $I$. Then for every $t>0$,
--
--   $$\mathbb P\big(\|F_I\|>\sqrt q\,\|F\|+c\sqrt t\big)\le r(s+1)e^{-t}.$$
--
--   Applied once to the rows and once to the columns, this gives the subsampling Lemma 2.2.
--
--   Differences from the source:
--   - encoding: c = max_j ‖f_j‖_2 → c with IsGreatest on the range of the column norms; reason: the same number, with no junk value of a supremum
--   - encoding: probability under a uniform choice → counting in multiplied form, #event against x · #sample (UniformProbLE / UniformProbGE); reason: the quotient would be 0/0 on an empty sample space; on a nonempty one the two forms are equivalent
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 2.4, p. 4, eq. (2)

import Mathlib
import Definitions.Def_MildHamilton_Main_Spectral

namespace MildHamilton.Main

/-- Lemma 2.4 (Muyesser, STOC 2027 submission #233, p. 4): sampling columns. `c` is the largest Euclidean
norm of a column of `F`. The probability is that of a uniformly random `k`-subset `I` of `[s]`. -/
theorem lemma_2_4 {r s k : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hk : k ≤ s)
    (F : Matrix (Fin r) (Fin s) ℝ) (c : ℝ)
    (hc : IsGreatest (Set.range fun j : Fin s => Real.sqrt (∑ i, F i j ^ 2)) c)
    (t : ℝ) (ht : 0 < t) :
    UniformProbLE (Finset.powersetCard k (Finset.univ : Finset (Fin s)))
      (fun I => Real.sqrt ((k : ℝ) / s) * opNorm F + c * Real.sqrt t <
        opNorm (F.submatrix id fun j : I => (j : Fin s)))
      ((r : ℝ) * ((s : ℝ) + 1) * Real.exp (-t)) := by sorry

end MildHamilton.Main
