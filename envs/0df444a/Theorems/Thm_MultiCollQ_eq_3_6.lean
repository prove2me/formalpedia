-- Prove2me | Theorems.Thm_MultiCollQ_eq_3_6
-- name    : MultiCollQ.eq_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:55.010448+00:00
-- url     : https://prove2.me/theorems/d7dc5526-5ae5-4a78-91fd-721522a2c695
-- title:
--   Display (3.6) — exact boundary counts $b_j(H)=\sum_{c:o_c(H)=j-1}(d_c-j+1)\le(k-j+1)(C_{j-1}(H)-C_j(H))$
-- statement:
--   Let the public buckets have sizes $d_c\le k$, let $2\le j\le k$, and fix an input $x$ and a partial injection $H$ with $x\notin\mathrm{dom}(H)$. The outputs $y\in Y_H=[N]\setminus\mathrm{im}(H)$ that increase the level-$j$ counter, $C_j(H[x\mapsto y])=C_j(H)+1$, are precisely the unused outputs in buckets with $o_c(H)=j-1$. Their number is
--
--   $$
--   b_j(H)=\sum_{c:\,o_c(H)=j-1}(d_c-j+1)\le(k-j+1)\bigl(C_{j-1}(H)-C_j(H)\bigr),
--   $$
--
--   with equality when every bucket has size $k$ (type $(k^n)$).
--
--   The count feeds Lemma 3.1 with $|E|=b_j(H)$ in Theorem 3.2 and Lemma 3.3.
--
--   **Formalization Note** All counts are cast to $\mathbb Z$, so the differences are integers as on the page.
--
--   Differences from the source:
--   - encoding: level $r$ ($2\le r\le k$) → level $j$ ($2\le j\le k$); reason: renaming; the paper applies (3.6) at every level $j$ in Lemma 3.3 (p.24)
--   - encoding: for type $(k^n)$ → every bucket has size $k$; reason: the buckets of type $(k^n)$ are exactly the partitions into buckets of size $k$
--   - encoding: natural-number counts → counts cast to $\mathbb Z$; reason: avoids truncated subtraction; same values
--   - encoding: $[N]$ and the buckets $Q_1,\dots,Q_h$ → `Fin N` (0-based) and a bucket map `b : Fin N → Fin h` with $Q_c=b^{-1}(c)$; reason: Lean convention; same instances
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), display (3.6), §3.1, p.21

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_MultiCollQ_levelCount

namespace MultiCollQ

open CompPermOracle

/-- Display (3.6), exact boundary counts (Peng, Hou, Dong, manuscript (Oct. 2026), §3.1, p.21), at a
level `j` with `2 ≤ j ≤ k` (the paper writes `r`; Lemma 3.3 uses it at every level `j`, p.24). Fix
an input `x` and a partial injection `H` with `x ∉ dom(H)`, and buckets of sizes `d_c ≤ k`. The
outputs `y ∈ Y_H` that increase `C_j` are precisely the unused outputs in buckets with
`o_c(H) = j − 1` (first conjunct); their number is `b_j(H) = Σ_{c : o_c(H) = j−1} (d_c − j + 1) ≤ (k − j + 1)(C_{j−1}(H) − C_j(H))`,
with equality when every bucket has size `k` (type `(k^n)`).

**Formalization Note.** Counts are cast to `ℤ`, so the differences are the paper's integers.
Increasing `C_j` means `C_j(H[x ↦ y]) = C_j(H) + 1`. -/
theorem eq_3_6 {N h k j : ℕ} (b : Fin N → Fin h) (hb : BucketsBounded b k) (hj : 2 ≤ j)
    (hjk : j ≤ k) (x : Fin N) (H : PartialPerm N) (hx : NotInDom H x) :
    ((freeIm H).filter fun y => levelCount b j (addPair H x y) = levelCount b j H + 1) =
        (freeIm H).filter (fun y => occ b H (b y) = j - 1) ∧
    ((((freeIm H).filter fun y => levelCount b j (addPair H x y) = levelCount b j H + 1).card : ℤ) =
        ∑ c ∈ Finset.univ.filter (fun c => occ b H c = j - 1), ((bucketSize b c : ℤ) - j + 1)) ∧
    (∑ c ∈ Finset.univ.filter (fun c => occ b H c = j - 1), ((bucketSize b c : ℤ) - j + 1) ≤
        ((k : ℤ) - j + 1) * ((levelCount b (j - 1) H : ℤ) - levelCount b j H)) ∧
    ((∀ c, bucketSize b c = k) →
      ∑ c ∈ Finset.univ.filter (fun c => occ b H c = j - 1), ((bucketSize b c : ℤ) - j + 1) =
        ((k : ℤ) - j + 1) * ((levelCount b (j - 1) H : ℤ) - levelCount b j H)) := by sorry

end MultiCollQ
