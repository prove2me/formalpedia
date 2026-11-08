-- Prove2me | Theorems.Thm_MaxCompForest_lemma_3_4
-- name    : MaxCompForest.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:07.128998+00:00
-- url     : https://prove2.me/theorems/7fe22383-31e0-46e1-898e-0645619b540a
-- title:
--   Lemma 3.4 — mass-multiaffine determinant support
-- statement:
--   There are one machine and absolute constants $C,a,b$ with the following property. Let $X$ be a finite nonempty set of $N$ items, item $x$ having positive rational $p_x$ and nonnegative rational masses $d_{x,1},\dots,d_{x,m}$, $m\ge1$, and let $0<\eta\le1$ be rational. The machine reads the items and $\eta$, and returns an unweighted subset $S\subseteq X$ with $|S|\le(256m/\eta)^{128m}$ such that for all rational columns $a_1,\dots,a_m\in\mathbb Q^{D}$ and every real positive semidefinite $D\times D$ matrix $B$, with $f_x(B)=p_x\det\big(B+\sum_i d_{x,i}a_ia_i^{\top}\big)$,
--   $$
--   \max_X f_x(B)\le(1+\eta)\max_S f_x(B).
--   $$
--   It halts within $\lceil(Cm/\eta)^{am}\rceil(N+B_{\mathrm{item}}+\mathrm{bits}(\eta)+2)^b$ steps, with $B_{\mathrm{item}}$ the longest encoded item.
--
--   The same subset serves every context $B$, though the best retained item may depend on $B$. This is what lets the recurrence discard candidates while staying near-optimal for every later extension.
--
--   Differences from the source:
--   - reading: “a deterministic algorithm … bit time” → one Mathlib multi-stack machine `TM2ComputableAux Sym Sym` on a fixed binary encoding; reason: the paper names no machine; a bit-operation algorithm and a multi-stack machine differ by a polynomial, which the time bound absorbs with changed absolute constants
--   - generalization: columns $a_1,\dots,a_m$ are fixed before the algorithm → the machine does not read the columns, and one set $S$ serves all $D$ and all columns; reason: “Only item moments enter the construction”, p.20: the moment vectors (3.18) depend on $p_x$ and $d_{x,i}$ only
--   - encoding: $\max_X f_x(B)\le(1+\eta)\max_S f_x(B)$ → for every $x$ there is $y\in S$ with $f_x(B)\le(1+\eta)f_y(B)$; reason: the same statement over a finite nonempty family
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Lemma 3.4, p.20

import Mathlib
import Definitions.Def_MaxCompForest_detScore
import Definitions.Def_MaxCompForest_itemBits
import Definitions.Def_MaxCompForest_encSupportIn
import Definitions.Def_MaxCompForest_encIndices
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_OnlineCRS_Combine_Sym
open OnlineCRS.Combine (Sym)
open CFLOutliers (OutputsWithin)
open OnlineCRS.Combine (encRat)

namespace MaxCompForest

/-- **Lemma 3.4 (Mass-multiaffine determinant support)**: one set `S`, computed from the item data alone, serves
every `D`, every rational columns and every real PSD `B`; `|S| ≤ (256m/η)^(128m)`; time
`⌈(Cm/η)^(am)⌉ · (N + B_item + bits(η) + 2)^b`, with `C`, `a`, `b` absolute.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.20.

**Formalization Note.** `max_X f_x(B) ≤ (1+η) max_S f_x(B)` is written `∀ x, ∃ y ∈ S, f_x(B) ≤ (1+η) f_y(B)` over
a finite nonempty family. -/
theorem lemma_3_4 :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (C a b : ℕ), 0 < C ∧
      ∀ (m N : ℕ) (η : ℚ) (p : Fin N → ℚ) (d : Fin N → Fin m → ℚ),
        1 ≤ m → 0 < N → 0 < η → η ≤ 1 → (∀ x, 0 < p x) → (∀ x i, 0 ≤ d x i) →
        ∃ S : List (Fin N), S.Nodup ∧
          (S.length : ℚ) ≤ (256 * (m : ℚ) / η) ^ (128 * m) ∧
          (∀ (D : ℕ) (A : Fin m → Fin D → ℚ) (B : Matrix (Fin D) (Fin D) ℝ), B.PosSemidef →
            ∀ x, ∃ y ∈ S, detScore A (p x) (d x) B ≤ (1 + (η : ℝ)) * detScore A (p y) (d y) B) ∧
          OutputsWithin M (encSupportIn η p d) (encIndices S)
            (⌈(((C : ℚ) * m) / η) ^ (a * m)⌉₊ *
              (N + itemBits p d + (encRat η).length + 2) ^ b) := by sorry

end MaxCompForest
