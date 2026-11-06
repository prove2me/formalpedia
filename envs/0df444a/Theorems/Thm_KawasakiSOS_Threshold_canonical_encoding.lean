-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_canonical_encoding
-- name    : KawasakiSOS.Threshold.canonical_encoding
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:11:24.479074+00:00
-- url     : https://prove2.me/theorems/92e5aac0-5212-4d94-99a5-aec1bcf50c18
-- title:
--   Lemma 4.11: the encoding of the canonical paths
-- statement:
--   There is an absolute constant $C>0$ such that for all $6\le k\le n$, every choice of canonical paths $\gamma_{xy}$, and every transition $e=(z,z')$, there is an injective map
--
--   $$\eta_e:\{(x,y):e\in\gamma_{xy}\}\to\Omega\times S_e,\qquad\eta_e(x,y)=(w,s),\qquad|S_e|\le N:=Ck^2(n+1)^9,$$
--
--   where $w$ is the complementary state of the segment containing the first occurrence of $e$ on $\gamma_{xy}$: $w=y$ in the opening, $w=x$ in the closing, and $w=w_S$ in the realization of a slide $S\to S'$. Moreover every $(x,y)$ with $e\in\gamma_{xy}$ satisfies
--
--   $$\max\{M(z),M(z')\}+M(w)\le M(x)+M(y)+2.$$
--
--   With the encoding lemma this gives congestion polynomial in both $n$ and $k$, which is the core of the polynomial upper bound.
--
--   Differences from the source:
--   - reading: the side information s is an itemized list → w is the page's state; a finite set S_e of the stated size and a value s making (w, s) injective are asserted to exist; reason: this is equivalent to each fibre of w having at most N elements, which is all Lemma 2.4 uses; the list is the proof of that claim
--   - reading: "All choices below are made canonically (for instance, smallest index first)" → every selection of paths satisfying IsCanonicalPath; reason: the source leaves the tie-break open; its own choice is one such selection
--   - reading: "an absolute constant C" → one constant C > 0, quantified before every parameter; reason: the O(·) of the source is read as an absolute constant, uniform in the displayed parameters
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.11, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_energy
import Definitions.Def_KawasakiSOS_Threshold_Segment
import Definitions.Def_KawasakiSOS_Threshold_IsCanonicalPath
import Definitions.Def_KawasakiSOS_Threshold_IsComplement
import Definitions.Def_KawasakiSOS_Threshold_joinStates
import Definitions.Def_KawasakiSOS_Threshold_firstSegment
open MarkovMixing DiaconisStroock.Poincare

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.11, p. 14 (PDF p. 15).

Formalization Notes:
- reading: the side information s is an itemized list → w is the page's state; a finite set S_e of the stated size and a value s making (w, s) injective are asserted to exist. This is equivalent to each fibre of w having at most N elements, which is all Lemma 2.4 uses; the list is the proof of that claim.
- reading: "All choices below are made canonically (for instance, smallest index first)" → every selection of paths satisfying IsCanonicalPath. The source leaves the tie-break open; its own choice is one such selection.
- reading: "an absolute constant C" → one constant C > 0, quantified before every parameter. The O(·) of the source is read as an absolute constant, uniform in the displayed parameters. -/
theorem canonical_encoding : ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) [NeZero k], 6 ≤ k → k ≤ n →
    ∀ (σ : Config n k → Config n k → List (ℕ × ℕ))
      (segs : Config n k → Config n k → List (Segment k × List (Config n k))),
      (∀ x y, x ≠ y → IsCanonicalPath x y (σ x y) (segs x y)) →
      ∀ e : Config n k × Config n k,
        ∃ (S : Type) (_ : Fintype S)
          (η : {p : Config n k × Config n k //
            p.1 ≠ p.2 ∧ e ∈ pathEdges (joinStates (segs p.1 p.2))} → Config n k × S),
          (Fintype.card S : ℝ) ≤ C * (k : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 9 ∧ Function.Injective η ∧
          ∀ p, (∃ seg, firstSegment (segs p.1.1 p.1.2) e = some seg ∧
                IsComplement p.1.1 p.1.2 seg (η p).1) ∧
            max (energy e.1.1) (energy e.2.1) + energy (η p).1.1 ≤
              energy p.1.1.1 + energy p.1.2.1 + 2 := by sorry

end KawasakiSOS.Threshold
