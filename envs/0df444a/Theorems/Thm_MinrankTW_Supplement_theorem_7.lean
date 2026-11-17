-- Prove2me | Theorems.Thm_MinrankTW_Supplement_theorem_7
-- name    : MinrankTW.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:08:35.258419+00:00
-- url     : https://prove2.me/theorems/2ae66ac4-2eba-4850-ad8d-7e120bc6754b
-- title:
--   Theorem 7 — Las Vegas recovery of a normalized fitting matrix of rank $\le r$ in expected time $q^{\min\{r(n-r),\sum_{i\in J}\deg_G(i)+2r\}}\mathrm{poly}(n)$
-- statement:
--   Suppose $G$ admits a normalized rank-$r$ fitting matrix with uniquely identifiable basis rows indexed by $J$. Given only $G$, $\mathbb F_q$ and $r$, a randomized algorithm finds a normalized fitting matrix of rank at most $r$ in expected time
--   $$
--   q^{\min\{r(n-r),\ \sum_{i\in J}\deg_G(i)+2r\}}\,\mathrm{poly}(n). \tag{30}
--   $$
--   In particular, for maximum degree $d=\deg(G)$ the time is $q^{r\min\{n-r,\,d+2\}}\,\mathrm{poly}(n)$.
--
--   Precisely: for every finite field with a fixed encoding there are one program of the logarithmic-cost RAM with fair coins and constants $C,k$ such that, for every graph $G$ on $n$ vertices, every $r$, every normalized fitting matrix $M^*$ of $G$ of rank $r$ and every $J$ indexing uniquely identifiable basis rows of $M^*$, the program run on $(G,r)$ is a Las Vegas algorithm: every halting run outputs a normalized fitting matrix of $G$ of rank at most $r$ (its entry codes, row by row), and the expected cost is at most both
--   $$
--   C\,q^{\min\{r(n-r),\ \sum_{i\in J}\deg_G(i)+2r\}}\,(n+1)^k
--   \qquad\text{and}\qquad
--   C\,q^{r\min\{n-r,\ \deg(G)+2\}}\,(n+1)^k .
--   $$
--   The algorithm sees neither $M^*$ nor $J$.
--
--   For bounded-degree graphs this improves the exponent $r(n-r)$ of classical kernel sampling to $O(r)$ per unit of degree.
--
--   Differences from the source:
--   - reading: "over a fixed finite field F_q" (§1.2, p.4) → for every finite field F with an encoding e : F ≃ Fin q there exist a program P and constants C, k; reason: the field is fixed before the algorithm; the constants depend on q only
--   - encoding: a randomized algorithm … in expected time → a program of the published log-cost RAM with fair coins TimeSpaceMA.Program satisfying the published SoftmaxAttnFD.LasVegasWithin (every halting run correct, expected bit cost ≤ the bound, non-halting runs cost +∞); reason: the algorithm of §D returns verified matrices and repeats inconclusive trials (p.23), a Las Vegas algorithm
--   - encoding: given only G, F_q and r → the input layout thm7Input (n, r, adjacency bits), G = fromRel edge; the field is fixed before the program; output cells i·n + j hold e(M_ij); reason: every graph has such an encoding
--   - encoding: uniquely identifiable basis rows indexed by J; deg_G(i); deg(G) → HasIdentifiableBasisRows G M* J; deg G i = number of neighbours; maxDeg G = maximum over vertices (0 when n = 0); reason: direct transcriptions of p.22 and p.23
--   - encoding: poly(n) → (n + 1)^k; reason: the input has n² + 2 cells; r ≤ n
--   - reading: the expected-time bound under the hypothesis → required for every witness M* and every J satisfying the hypothesis; behaviour on other inputs unconstrained; reason: p.23: the expected-time bounds concern yes-instances; the algorithm needs neither M* nor J
--   - reading: the comparison "compared to q^{r(n−r)} poly(n) for the classical kernel-sampling method" → not stated; reason: a comparison with another algorithm, not a claim of the theorem; the bound q^{r(n−r)} is the first term of the minimum
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 7, p.22, Eq. (30) (proof via Proposition 2, pp.24–26)

import Mathlib
import Definitions.Def_MinrankTW_IsNormalizedFit
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_MinrankTW_Supplement_IdentifiableRows
import Definitions.Def_MinrankTW_Supplement_thm7Input

namespace MinrankTW.Supplement

/-- **Theorem 7** (Faster recovery from identifiable kernel equations), Perles–Weinstein, *Efficient
Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript
(sha256 32a91384…c57991), p.22, Eq. (30) (proof via Proposition 2, pp.24–26). Suppose `G` admits a
normalized rank-`r` fitting matrix with uniquely identifiable basis rows indexed by `J`. Given only
`G`, `F_q` and `r`, a randomized algorithm finds a normalized fitting matrix of rank at most `r` in
expected time `q^{min{r(n−r), Σ_{i∈J} deg_G(i) + 2r}} poly(n)`; in particular, for maximum degree
`d = deg(G)`, in time `q^{r·min{n−r, d+2}} poly(n)`.

**Formalization Note** For every finite field `F` with encoding `e` there are one program `P` of
the published logarithmic-cost RAM with fair coins (`TimeSpaceMA.Program`) and constants `C, k`
such that for all `n, r`, every graph table `edge` (`G = fromRel edge`), every normalized fitting
matrix `M*` of `G` of rank `r` and every `J` indexing uniquely identifiable basis rows of `M*`, the
program run on `thm7Input n r edge` (which contains neither `M*` nor `J`) is Las Vegas
(`SoftmaxAttnFD.LasVegasWithin`: every halting run outputs, in cells `i·n + j`, the codes `e(M_ij)`
of a normalized fitting matrix `M` of `G` of rank at most `r`) within expected cost
`C·q^{min(r(n−r), Σ_{i∈J} deg_G(i) + 2r)}·(n + 1)^k`, and within
`C·q^{r·min(n−r, deg(G)+2)}·(n + 1)^k`. -/
theorem theorem_7 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (e : F ≃ Fin (Fintype.card F)) :
    ∃ (P : TimeSpaceMA.Program) (C k : ℕ), ∀ (n r : ℕ) (edge : Fin n → Fin n → Bool)
      (Mstar : Matrix (Fin n) (Fin n) F) (J : Finset (Fin n)),
      MinrankTW.IsNormalizedFit (SimpleGraph.fromRel fun u v => edge u v = true) Mstar →
      Mstar.rank = r →
      HasIdentifiableBasisRows (SimpleGraph.fromRel fun u v => edge u v = true) Mstar J →
      SoftmaxAttnFD.LasVegasWithin P (thm7Input n r edge)
          (fun out => ∃ M : Matrix (Fin n) (Fin n) F,
            MinrankTW.IsNormalizedFit (SimpleGraph.fromRel fun u v => edge u v = true) M ∧
            M.rank ≤ r ∧ ∀ i j : Fin n, out ((i : ℕ) * n + j) = (e (M i j) : ℕ))
          ((C : ℝ) * (Fintype.card F : ℝ) ^ (min (r * (n - r))
              (∑ i ∈ J, deg (SimpleGraph.fromRel fun u v => edge u v = true) i + 2 * r)) *
            ((n : ℝ) + 1) ^ k) ∧
      SoftmaxAttnFD.LasVegasWithin P (thm7Input n r edge)
          (fun out => ∃ M : Matrix (Fin n) (Fin n) F,
            MinrankTW.IsNormalizedFit (SimpleGraph.fromRel fun u v => edge u v = true) M ∧
            M.rank ≤ r ∧ ∀ i j : Fin n, out ((i : ℕ) * n + j) = (e (M i j) : ℕ))
          ((C : ℝ) * (Fintype.card F : ℝ) ^ (r * min (n - r)
              (maxDeg (SimpleGraph.fromRel fun u v => edge u v = true) + 2)) *
            ((n : ℝ) + 1) ^ k) := by sorry

end MinrankTW.Supplement
