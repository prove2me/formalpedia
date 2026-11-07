-- Prove2me | Theorems.Thm_MonDepMW_lemma_8_1
-- name    : MonDepMW.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:08.546203+00:00
-- url     : https://prove2.me/theorems/b3f4f23b-aba3-4543-b31f-a5de58d72804
-- title:
--   Lemma 8.1 — mismatch bounds reachability in $G\oplus\sigma$
-- statement:
--   Let $r\geqslant1$, $G$ a graph and $B\subseteq V(G)$. Put $\mathcal P=\mathcal T_{r+1}(G,B)$ and $\mathcal Q=\mathcal T_1(G,B)$, let $\sigma\subseteq\mathcal Q\times\mathcal Q$ be symmetric and let $m$ be the mismatch of $\sigma$ with respect to $\mathcal P$. Then for every vertex $u$, at most
--   $$(m+1)^r$$
--   parts of $\mathcal Q$ contain a vertex at distance at most $r$ from $u$ in $G\oplus\sigma$.
--
--   It translates the mismatch of Corollary 7.8 into the radius-$r$ ball bound of the Damping Theorem.
--
--   Differences from the source:
--   - generalization: m the mismatch of σ → every m bounding the mismatch; reason: at the exact mismatch, which may be 0, this is the source’s claim
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 8.1, p.32

import Mathlib
import Definitions.Def_MonDepMW_rType
import Definitions.Def_MonDepMW_IsFlip
import Definitions.Def_MonDepMW_MismatchLE

set_option autoImplicit false

namespace MonDepMW

/-- **Lemma 8.1.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.32: "Let r ∈ N, G be a graph, and B be a subset of vertices of G. Denote 𝒫 := 𝒯r+1(G, B) and
𝒬 := 𝒯1(G, B). Further, let σ ⊆ 𝒬 × 𝒬 be a symmetric binary relation and m be the mismatch of σ with respect to 𝒫. Then for every
vertex u of G, there are at most (m + 1)^r parts of 𝒬 that contain a vertex that is at distance at most r from u in the graph
G ⊕ σ."

**Formalization Note.** Posed for every `m` bounding the mismatch: this contains the exact mismatch, which may be `0`, and the
bound is monotone in `m`. -/
theorem lemma_8_1 (r : ℕ) (hr : 1 ≤ r) {n : ℕ} (G : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (σ : Quotient (oneType G B) → Quotient (oneType G B) → Prop) (hσ : ∀ X Y, σ X Y → σ Y X) (m : ℕ)
    (hm : MismatchLE G (oneType G B) (rType G B (r + 1)) σ m) (u : Fin n) :
    partsHit (oneType G B) (ball (flipBy G (oneType G B) σ hσ) r u) ≤ (m + 1) ^ r := by sorry

end MonDepMW
