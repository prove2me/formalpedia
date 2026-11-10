-- Prove2me | Theorems.Thm_NearLogSetCover966_Main_lemma_3_1
-- name    : NearLogSetCover966.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:22:01.672984+00:00
-- url     : https://prove2.me/theorems/c750f3b4-49af-4a70-8540-3a7efe6914ae
-- title:
--   Lemma 3.1 — local acceptance identity
-- statement:
--   Let $n\ge0$, let $L\subseteq\{0,1\}^n$, and let $\Phi$ be any monotone Boolean function. For every assignment $x$,
--
--   $$\Phi(x)\le\bigwedge_{z\in L}\left(\Phi(z)\lor\bigvee_{a:z_a=0}x_a\right).$$
--
--   Equality holds for every $x\in L$. The statement retains both the inequality on all assignments and the identity on the designated family, including the empty family and zero-variable cases. It is the local acceptance identity used by the Label Cover conversion.
--
--   **Formalization Note** Boolean order is $0\le1$. Universal quantification represents finite conjunction, and existence represents disjunction, so empty gates have their standard truth values.
--
--   Differences from the source:
--   - generalization: a monotone circuit on n Boolean variables → any monotone Boolean function on the same finite cube; reason: every source circuit has such a function; both conclusions are preserved without a circuit-size claim
-- source:
--   Bingkai Lin, Xin Zheng, STOC 2027 submission #966 (October 2026), Lemma 3.1, printed p. 12, PDF p. 14

import Definitions.Def_NearLogSetCover966_Main_Core

set_option autoImplicit false

namespace NearLogSetCover966.Main

theorem lemma_3_1 (n : ℕ) (L : Set (Bits n)) (Φ : Bits n → Bool)
    (hΦ : Monotone Φ) :
    (∀ x : Bits n, Φ x ≤ localAcceptance L Φ x) ∧
      ∀ x ∈ L, Φ x = localAcceptance L Φ x := by sorry

end NearLogSetCover966.Main
