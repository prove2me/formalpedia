-- Prove2me | Theorems.Thm_HarelTarjan_Compressed_lemma9_plies
-- name    : HarelTarjan.Compressed.lemma9_plies
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:55:33.938587+00:00
-- url     : https://prove2.me/theorems/eb26143b-0783-48a8-8cd0-c2bd9406574e
-- title:
--   Lemma 9 (explicit form proved on p. 345) — ply three ≤ 4n/lg n, ply two ≤ 4n/lg⁽²⁾ n, ply-one components ≤ lg⁽²⁾ n
-- statement:
--   Let $T$ be a rooted tree on $n \ge 4$ vertices, $C$ its compressed tree, and divide $C$ into plies one, two and three by rank, with thresholds $\lfloor \lg^{(3)} n\rfloor$ and $\lfloor \lg^{(2)} n \rfloor$. Then:
--
--   1. Ply three contains at most $4n/\lg n$ vertices:
--   $$|\text{ply three}| \le \frac{4n}{\lg n}.$$
--   2. Ply two contains at most $4n/\lg^{(2)} n$ vertices:
--   $$|\text{ply two}| \le \frac{4n}{\lg^{(2)} n}.$$
--   3. Each connected component of ply one is a subtree of $C$ containing at most $\lg^{(2)} n$ vertices. Precisely: for every vertex $v$ in ply one, all descendants of $v$ in $C$ lie in ply one, and
--   $$\mathrm{size}_C(v) \le \lg^{(2)} n .$$
--
--   The paper states Lemma 9 with $O(n/\log n)$ and $O(n/\log^{(2)} n)$; its proof on p. 345 establishes the explicit constants $4$ and $4$ given here. The lemma is what makes the depth problem on $C$ solvable with linear preprocessing: the tables for plies two and three have total size $O(n)$, and ply one splits into tiny subtrees.
--
--   **Formalization Note** $\lg$ is `Real.logb 2`, $n$ is `Fintype.card V`, and the plies use the iterated `Nat.log` thresholds of the definition `Plies` (equal to the real floors for $n \ge 4$). The hypothesis $n \ge 4$ is added: it is not on the page, where the $O(\cdot)$ hides it, and it makes $\lg n \ge 2$ and $\lg^{(2)} n \ge 1$, so that the divisions are honest (Lean's $x/0 = 0$) and $\lg^{(3)} n \ge 0$. Part 3 is the vertex-wise reading of "each connected component of ply one is a subtree of $C$ with at most $\lg^{(2)} n$ vertices": since ply one is closed under taking $C$-descendants, the component of a ply-one vertex is the $C$-subtree of its shallowest ply-one ancestor, and that subtree's size is bounded because its root lies in ply one.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 345, Lemma 9 and its proof

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree
import Definitions.Def_HarelTarjan_Compressed_Plies

namespace HarelTarjan.Compressed

theorem lemma9_plies {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (hn : 4 ≤ Fintype.card V) :
    ((ply3 T).card : ℝ) ≤ 4 * (Fintype.card V : ℝ) / Real.logb 2 (Fintype.card V) ∧
    ((ply2 T).card : ℝ) ≤
      4 * (Fintype.card V : ℝ) / Real.logb 2 (Real.logb 2 (Fintype.card V)) ∧
    ∀ v ∈ ply1 T,
      (∀ u : V, IsAncestorC T v u → u ∈ ply1 T) ∧
      (sizeC T v : ℝ) ≤ Real.logb 2 (Real.logb 2 (Fintype.card V)) := by sorry

end HarelTarjan.Compressed
