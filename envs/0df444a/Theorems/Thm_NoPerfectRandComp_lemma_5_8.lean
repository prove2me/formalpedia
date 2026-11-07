-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_5_8
-- name    : NoPerfectRandComp.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:47.522641+00:00
-- url     : https://prove2.me/theorems/51233f8c-0532-473f-baae-028f27646db4
-- title:
--   Lemma 5.8 — hardness of the central layers, success $\le 3/5$ at depth $\lfloor q^2s/10^6\rfloor$
-- statement:
--   Let $q = 2^s - 1$ with $s \ge 1000$, and let $T = \lfloor q^2 s / 10^6 \rfloor$. There is a fixed distribution on $q$-tuples of $q\times q$ pointer arrays such that every full-cell algorithm of depth at most $T$ computes $\mathrm{Maj}_q \circ \Pi_q^{\,q}$ with success probability at most $3/5$ under it.
--
--   Through the private encoding (Lemma 5.9) this becomes the inner lower bound (19).
--
--   **Formalization Note** A full-cell algorithm queries whole pointer cells: it is a distribution over decision trees whose queries return elements of $A_q$. The distribution is fixed before the algorithm; randomized algorithms are included, deterministic ones being point masses.
--
--   Differences from the source: none.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 5.8, p.23; T from Eq. (24), p.22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_maj
import Definitions.Def_NoPerfectRandComp_PiQ

namespace NoPerfectRandComp

/-- Lemma 5.8 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.23 (hardness of the central layers): for `q = 2ˢ − 1` and `s ≥ 1000`,
every full-cell algorithm of depth at most `T = ⌊q² s / 10⁶⌋` ((24), p.22) has success at most
`3/5` under a fixed distribution on inputs to `Maj_q ∘ Π_q^q`.

**Formalization Note** A full-cell algorithm queries a whole pointer cell: it is a distribution
over decision trees on the coordinates `(block i, cell)` with answers in `PtrCell q`. The
distribution is fixed before the algorithm. Randomized algorithms are included (the proof's last
sentence); deterministic ones are point masses. `T` is natural-number division. -/
theorem lemma_5_8 (s q : ℕ) (hs : 1000 ≤ s) (hq : q = 2 ^ s - 1) :
    ∃ μ : PMF (Fin q × (Fin q × Fin q) → PtrCell q),
      ∀ A : QAlgorithms.RandDecisionTree (Fin q × (Fin q × Fin q)) (PtrCell q) Bool,
        QAlgorithms.RandMakesAtMost A (q ^ 2 * s / 10 ^ 6) →
        ∑ x, (μ x).toReal *
          QAlgorithms.successProb A x (maj q (fun i => PiQ q (fun c => x (i, c))))
            ≤ 3 / 5 := by sorry

end NoPerfectRandComp
