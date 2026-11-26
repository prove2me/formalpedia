-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_twentyfour_lower
-- name    : LefebvreVariations.kissing_number_twentyfour_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:41:20.075557+00:00
-- url     : https://prove2.me/theorems/e95da47c-beee-4f55-9a72-cdb6ba24929c
-- title:
--   Lefebvre's variations, No. 99 — on a theme by Conway and Sloane: the Leech lattice gives 196560 touching balls in dimension 24
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the constructive half of the kissing number in dimension $24$: the Leech lattice supplies $196560$ unit balls touching a unit ball.
--
--   A *kissing configuration* in $\mathbb{R}^{d}$ is a finite set of unit vectors with pairwise inner products at most $\tfrac12$ (equivalently, centres of non-overlapping unit balls touching a central unit ball, after rescaling). The kissing number $\tau(d)$ is the largest size of such a set. The statement is
--
--   $$
--   196560 \;\le\; \tau(24).
--   $$
--
--   The classical witness is the set of minimal vectors of the Leech lattice $\Lambda_{24}$, written in coordinates scaled by $\sqrt{8}$ (so that minimal vectors have squared norm $32$), with $\mathcal{G}$ the extended binary Golay code of length $24$ (dimension $12$, weights $0, 8, 12, 16, 24$, $759$ words of weight $8$):
--
--   - $(\pm 2)^{8}0^{16}$: the support is a weight-$8$ word of $\mathcal{G}$ (an octad) and the number of minus signs is even: $759 \cdot 2^7 = 97152$ vectors;
--   - $(\mp 3, \pm 1^{23})$: take $c \in \mathcal{G}$, put the sign $(-1)^{c_i}$ on coordinate $i$ (entries $\pm 1$), then replace the entry at one position $j$ by its value minus $4$ times its sign: $24 \cdot 2^{12} = 98304$ vectors;
--   - $(\pm 4, \pm 4, 0^{22})$: $4 \binom{24}{2} = 1104$ vectors.
--
--   These $196560$ vectors are pairwise distinct, have squared norm $32$, and any two distinct ones have inner product at most $16$ (the possible normalised inner products are $-1, -\tfrac12, -\tfrac14, 0, \tfrac14, \tfrac12$). Dividing by $\sqrt{32}$ gives a kissing configuration with $196560$ points.
--
--   The matching upper bound $\tau(24) \le 196560$ is the Delsarte–Levenshtein linear-programming bound: the degree-$10$ polynomial $f(t) = (t+1)(t+\tfrac12)^2(t+\tfrac14)^2 t^2 (t-\tfrac14)^2 (t-\tfrac12)$ is $\le 0$ on $[-1,\tfrac12]$, has positive Gegenbauer coefficients $c_k$ in dimension $24$ with $c_0 = \tfrac{15}{1490944}$ and $f(1) = \tfrac{2025}{1024}$, and $f(1)/c_0 = 196560$.
--
--   **Formalization Note** The statement is `(196560 : ℕ∞) ≤ KissingNumber.kissingNumber 24`, where `kissingNumber 24` is the supremum in `ℕ∞` of the cardinalities of `KissingConfig 24` (finite sets of unit vectors of `EuclideanSpace ℝ (Fin 24)` with pairwise inner products at most `1/2`), as in `Definitions.Def_KissingNumber`. To prove it one must exhibit a `KissingConfig 24` with at least $196560$ points (for instance the rescaled Leech minimal vectors above). A direct kernel check of all pairs is out of reach ($\approx 1.9 \cdot 10^{10}$ inner products), so a proof needs the structure of the Golay code (even intersections of codewords, octads meeting in $0, 2, 4, 8$ points).
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `KissingNumber.kissing_number_twentyfour` ($\tau(24) = 196560$). The upper bound $\tau(24) \le 196560$ is proved in Lean from Delsarte's linear-programming argument with the polynomial above (its Gegenbauer expansion is checked by `ring`), using the already published variation `LefebvreVariations.gegenbauer_positive_definite` for $n=24$ and $k \le 10$. What is left is exactly this lower bound. It is an ingredient of the base statement (one of its two halves), not the whole of it.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). J. Leech, Notes on sphere packings, Canad. J. Math. 19 (1967), 251–267 (the Leech lattice and its 196560 minimal vectors). J. H. Conway, A characterisation of Leech's lattice, Invent. Math. 7 (1969), 137–142. J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, Chapter 3 (the Golay code), Chapter 4 (the Leech lattice, its minimal vectors in the three shapes above) and Chapter 13 (Levenshtein's bound, τ(24) = 196560). Upper bound: V. I. Levenshtein, On bounds for packings in n-dimensional Euclidean space, Soviet Math. Dokl. 20 (1979), 417–421; A. M. Odlyzko and N. J. A. Sloane, New bounds on the number of unit spheres that can touch a unit sphere in n dimensions, J. Combin. Theory Ser. A 26 (1979), 210–214. Origin of this statement: it is the missing step of a reduction of KissingNumber.kissing_number_twentyfour (τ(24) = 196560). In that reduction the upper bound τ(24) ≤ 196560 is proved by Delsarte's linear-programming argument with the degree-10 polynomial f(t) = (t+1)(t+1/2)^2(t+1/4)^2 t^2 (t-1/4)^2 (t-1/2), whose exact expansion f = 15/1490944 C_0 + 45/4100096 C_1 + 15/1949696 C_2 + 435/79659008 C_3 + 6927/2230452224 C_4 + 489/278806528 C_5 + 17747/22435725312 C_6 + 261/756760576 C_7 + 5/44808192 C_8 + 3/94595072 C_9 + 1/189190144 C_10 in the Gegenbauer polynomials C_k^{(11)} is verified by `ring`, from the published Lefebvre variation LefebvreVariations.gegenbauer_positive_definite (n = 24, k ≤ 10). The remaining lower bound is this statement.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations
theorem kissing_number_twentyfour_lower : (196560 : ℕ∞) ≤ KissingNumber.kissingNumber 24 := by sorry
end LefebvreVariations
