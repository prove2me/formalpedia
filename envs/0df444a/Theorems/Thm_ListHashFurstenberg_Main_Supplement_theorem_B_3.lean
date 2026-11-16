-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_Supplement_theorem_B_3
-- name    : ListHashFurstenberg.Main.Supplement.theorem_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:59:20.348271+00:00
-- url     : https://prove2.me/theorems/6485d880-dc83-46b4-ba75-c3c879a553f9
-- title:
--   Theorem B.3 — maximum-load tail
-- statement:
--   Let $F$ be a finite field of order $q$, let $t,u,\ell$ be integers with $t\ge1$ and $u\ge\ell\ge1$, and let $S\subseteq F^u$ have exactly $q^\ell$ elements. For $h:F^u\to F^\ell$ uniformly random among all linear maps, write $M(S,h)=\max_b|S\cap h^{-1}(b)|$. Then
--
--   $$\Pr\!\left[M(S,h)\ge q^{15+\log_2\log_2q+t+\log_2t}\right]<2q^{-t(t-\log_2\ell+\log_2t)}.$$
--
--   The event includes equality at its real threshold, while the probability bound is strict. This companion theorem gives the appendix's maximum-load tail estimate; its two supporting results are Lemmas B.1 and B.2(a).
--
--   Differences from the source:
--   - encoding: finite fields F_q and coordinate spaces F_q^u → an arbitrary finite field F with q = Fintype.card F and vectors Fin u → F; reason: every prime-power field is included, with exactly the same finite sets and uniform maps
--   - encoding: Pr over all linear maps, with real powers and base-two logarithms → published probLin and maxLoad, Real.rpow and Real.logb 2; reason: the threshold and probability bound use exactly the printed exponents and directions, including the strict probability bound
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, STOC 2027 submission #1578 (October 2026), Theorem B.3, printed p.36 = PDF p.36; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1578.pdf; SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9

import Mathlib
import Definitions.Def_LinMaxLoad_probLin
import Definitions.Def_LinMaxLoad_maxLoad

open Classical

namespace ListHashFurstenberg.Main.Supplement

/-- Theorem B.3, p.36: all linear maps, closed upper-tail event, strict probability bound. -/
theorem theorem_B_3 (F : Type*) [Field F] [Fintype F]
    (t u ℓ : ℕ) (ht : 1 ≤ t) (hℓ : 1 ≤ ℓ) (hℓu : ℓ ≤ u)
    (S : Finset (Fin u → F)) (hcard : S.card = Fintype.card F ^ ℓ) :
    let q : ℝ := Fintype.card F
    LinMaxLoad.probLin F (Fin u → F) ℓ
      (fun h => Real.rpow q (15 + Real.logb 2 (Real.logb 2 q) + (t : ℝ) +
          Real.logb 2 (t : ℝ)) ≤ (LinMaxLoad.maxLoad (h : (Fin u → F) → (Fin ℓ → F)) S : ℝ)) <
      2 * Real.rpow q (-(t : ℝ) * ((t : ℝ) - Real.logb 2 (ℓ : ℝ) +
        Real.logb 2 (t : ℝ))) := by sorry

end ListHashFurstenberg.Main.Supplement
