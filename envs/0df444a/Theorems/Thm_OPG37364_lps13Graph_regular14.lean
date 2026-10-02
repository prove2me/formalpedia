-- Prove2me | Theorems.Thm_OPG37364_lps13Graph_regular14
-- name    : OPG37364.lps13Graph_regular14
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T14:09:08.144826+00:00
-- url     : https://prove2.me/theorems/a1b44539-4a01-4515-b3fe-7e0b60624a02
-- title:
--   Fourteen-regular fixed-p=13 LPS Cayley graph on PGL₂
-- statement:
--   Let $q>13$ be prime and choose $i\in\mathbb F_q$ with $i^2=-1$. Let $S$ be the projective images of the fourteen matrices
--
--   $$M_i(a)=\begin{pmatrix}a_0+i a_1&a_2+i a_3\\-a_2+i a_3&a_0-i a_1\end{pmatrix},$$
--
--   where $a$ ranges over $(1,\pm2,\pm2,\pm2)$ and the six tuples $(3,\pm2,0,0)$ with the nonzero imaginary coordinate in any of the three positions. Each matrix has determinant $13$. Projectivization is in $\operatorname{PGL}_2(\mathbb F_q)$, modulo all nonzero scalar matrices.
--
--   Then the simple Cayley graph on this finite projective group, with edges $v\sim vs$ for $s\in S$, is $14$-regular: every vertex has exactly fourteen neighbors. The formal conclusion is the original OPG37364 set-cardinality predicate `IsRegularOfDegree`, using `neighborSet.encard`.
--
--   The proof establishes distinct projective images, exclusion of the identity and inverse closure through quaternion conjugation. The chosen root is a transparent parameter, not a graph-property assumption. For primes from the fixed-13 arithmetic selection lemma, $q\equiv1\pmod4$ supplies a root and $(13/q)=-1$ identifies the PGL branch of the LPS construction. Nonresiduosity is unnecessary for regularity. Connectedness, bipartiteness, girth and spectral estimates are outside this theorem.
-- source:
--   Lubotzky, Phillips and Sarnak, Ramanujan graphs, Combinatorica 8 (1988), p. 262, https://doi.org/10.1007/BF02126799 (positive odd real coordinate and even imaginary coordinates). Davidoff, Sarnak and Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs, Proposition 2.5.2 (matrix formula with x=i, y=0), Definition 4.1.1 (right Cayley convention), and Section 4.2, especially Lemma 4.2.1 and Remark 4.2.3(c), https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . Fixed-p=13 structural formalization of classical mathematics.

import Definitions.Def_opg37364_lps13
set_option autoImplicit false

namespace OPG37364

theorem lps13Graph_regular14 {q : ℕ} [Fact q.Prime]
    (hq : 13 < q) (i : LPS13Root q) :
    IsRegularOfDegree (lps13Graph hq i) 14 := by sorry

end OPG37364
