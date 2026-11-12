-- Prove2me | Theorems.Thm_NetUnrelEst_Main_eq_7
-- name    : NetUnrelEst.Main.eq_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:19.953199+00:00
-- url     : https://prove2.me/theorems/739709a6-b569-4261-bf78-e6054134522d
-- title:
--   §2.3, Eq. (7) — the expected number of failed cuts exceeds u by at most half the ordered pair sum
-- statement:
--   Let $G$ be a connected multigraph with $n\ge2$ vertices whose edges fail independently with probabilities $p_e\in[0,1]$, and let $u$ be the probability that the working edges leave $G$ disconnected. Write $z=\sum_C a_C$ for the expected number of failed cuts and $x=\sum_{C\ne C'}a_{C\cup C'}$ for the sum over ordered pairs of distinct cuts. A final state whose working graph has $K$ components has exactly $2^{K-1}-1$ failed cuts, and consequently
--   $$0\le z-u\le \frac x2.\tag{7}$$
--
--   The difference $z-u$ is the overcount of the union bound over cuts, and (7) bounds it by pairs of cuts that fail together. With Theorem 2.3 this shows that $z$ and $u$ agree to within $O(u^{3/2})$ for very reliable graphs.
--
--   **Formalization Note.** A failed cut is a cut all of whose crossing edges are in the failure set $F$; $K$ is the number of connected components of the working graph of $F$. Cuts are unordered bipartitions, and ordered pairs are enumerated as $C$ and then $C'\ne C$.
--
--   Differences from the source:
--   - generalization: the graph of §2.3 (the reduced graph G of §2.1, 0 < p_e < 1) → any connected multigraph on Fin n with n ≥ 2 (self-loops and parallel edges allowed) and p ∈ [0,1]^m; reason: the counting identity and (7) hold for every failure law; the reduced graph with 0 < p_e < 1 is one instance
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 10, §2.3, Eq. (7)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **§2.3, Eq. (7).** For a connected multigraph with `n ≥ 2` vertices and failure probabilities
`p ∈ [0,1]^m`: a failure set whose working graph has `K` components has exactly `2^{K−1} − 1`
failed cuts, and `0 ≤ z − u ≤ x/2`, where `z = Σ_C a_C` and `x = Σ_{C ≠ C'} a_{C ∪ C'}` over
ordered pairs. Sun 2027, p. 10, (7). -/
theorem eq_7 {n m : ℕ} (ends : Ends n m) (hn : 2 ≤ n) (hconn : IsConnectedGraph ends)
    (p : Fin m → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
    (∀ F : Finset (Fin m), numFailedCuts ends F = 2 ^ (numComponents ends F - 1) - 1) ∧
    0 ≤ zSum ends p - unrel ends p ∧ zSum ends p - unrel ends p ≤ xSum ends p / 2 := by sorry

end NetUnrelEst.Main
