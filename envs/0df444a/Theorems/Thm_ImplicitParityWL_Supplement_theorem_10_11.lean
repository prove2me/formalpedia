-- Prove2me | Theorems.Thm_ImplicitParityWL_Supplement_theorem_10_11
-- name    : ImplicitParityWL.Supplement.theorem_10_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:32:49.4992+00:00
-- url     : https://prove2.me/theorems/1fffa9f8-7d60-40d5-9598-e74944e98a38
-- title:
--   Theorem 10.11 — witness size $\le k(kM)^r$ from $r$ rounds
-- statement:
--   Fix $k\ge2$ and colored graphs $G,H$, and let $r\ge0$. If $k$-WL distinguishes $G$ and $H$ after $r$ rounds, then some colored graph $F$ with $\mathrm{tw}(F)\le k$ and
--   $$|V(F)|\le k(kM)^r,\qquad M:=|V(G)|^k+|V(H)|^k,$$
--   satisfies $\hom(F,G)\ne\hom(F,H)$.
--
--   With the Döring–Neuen bound on the stabilization round this gives witnesses of size $2^{O_k(n^{k-1}\log n)}$ (Corollary 10.12), so Theorem 1.4 is tight up to a logarithmic factor in the exponent.
--
--   **Formalization Note** "Distinguishes after $r$ rounds" means that the round-$r$ histograms of $k$-tuple colors differ. $F$ is colored over the colors of $G$ and $H$, on a finite vertex set, $\hom$ counts color-preserving homomorphisms, and $\mathrm{tw}(F)\le k$ is the published `RobersonCx.TwLE`.
--
--   Differences from the source:
--   - reading: some graph F → a colored graph F over the color type of G and H; reason: hom(F, ·) counts color-preserving homomorphisms (§10.4), and the proof ends with a colored F′ of the same order and treewidth
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Theorem 10.11, p.61 (standing assumptions §10.4, p.60)

import Mathlib
import Definitions.Def_ImplicitParityWL_WLColor
import Definitions.Def_ImplicitParityWL_Supplement_Homomorphism

namespace ImplicitParityWL

namespace Supplement

/-- **Theorem 10.11** (Witness size from rounds; Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for
the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.61): fix
`k ≥ 2` and colored graphs `G`, `H` (§10.4, p.60), and let `r ≥ 0`. If `k`-WL distinguishes `G` and `H`
after `r` rounds, then some graph `F` with `tw(F) ≤ k` and `|V(F)| ≤ k(kM)^r` for
`M := |V(G)|^k + |V(H)|^k` satisfies `hom(F, G) ≠ hom(F, H)`.

**Formalization Note** "Distinguishes after `r` rounds" is `DistinguishesAfter G H k r`: the round-`r`
histograms differ. `F` is a colored graph over the color type of `G` and `H` (the end of the proof turns
the witness into a colored graph), on a finite vertex type `U`; `tw(F) ≤ k` is the published
`RobersonCx.TwLE`, and `hom` counts color-preserving homomorphisms. -/
theorem theorem_10_11 (k : ℕ) (hk : 2 ≤ k) {K V W : Type} [Fintype V] [Fintype W]
    (G : ColoredGraph K V) (H : ColoredGraph K W) (r : ℕ) (hr : DistinguishesAfter G H k r) :
    ∃ (U : Type) (_ : Fintype U) (F : ColoredGraph K U), RobersonCx.TwLE F.graph k ∧
      Fintype.card U ≤ k * (k * (Fintype.card V ^ k + Fintype.card W ^ k)) ^ r ∧
      homCount F G ≠ homCount F H := by sorry

end Supplement

end ImplicitParityWL
