-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_corollary_3_4
-- name    : ListHashFurstenberg.Main.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:57.73217+00:00
-- url     : https://prove2.me/theorems/46983edd-f235-4bad-82b8-5b46c3829e8c
-- title:
--   Corollary 3.4 — max-load tail bound for linear hashing, every universe dimension
-- statement:
--   Let $F$ be a finite field with $q=|F|$ elements, let $u\ge\ell\ge1$ be integers and let $h:F^u\to F^\ell$ be a uniformly random $F$-linear map (a uniformly random $\ell\times u$ matrix, of any rank). For a map $h$ and a finite set $S$, the **max load** $M(S,h)=\max_b|h^{-1}(b)\cap S|$ is the largest number of elements of $S$ sent to a single point. Then for every real $T\ge8q$ and every $S\subseteq F^u$,
--
--   $$\Pr_h[M(S,h)\ge T]\le\frac{9|S|}{q^{\ell}T}\exp\!\left(\frac{8q(\ell+2\lceil\log_qT\rceil)}{T}\right).$$
--
--   This is the tail bound that Theorem 4.4 applies to a Hamming ball; it holds with no lower bound on $u$ in terms of the other parameters.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Corollary 3.4, p.21

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin

namespace ListHashFurstenberg.Main

/-- Corollary 3.4, p.21 of Kumar–Mon, STOC 2027 submission #1578 (general tail bound for all
`u`). Let `u ≥ ℓ ≥ 1` and let `h : F^u → F^ℓ` be a uniformly random `F`-linear map. For any
`T ≥ 8q` and any `S ⊆ F^u`, `Pr[M(S, h) ≥ T] ≤ (9|S| / (q^ℓ T)) · exp(8q(ℓ + 2⌈log_q T⌉) / T)`. -/
theorem corollary_3_4 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (u ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hu : ℓ ≤ u) (T : ℝ) (hT : 8 * (Fintype.card F : ℝ) ≤ T)
    (S : Finset (Fin u → F)) :
    LinMaxLoad.probLin F (Fin u → F) ℓ (fun h => T ≤ (LinMaxLoad.maxLoad h S : ℝ)) ≤
      9 * S.card / ((Fintype.card F : ℝ) ^ ℓ * T) *
        Real.exp (8 * (Fintype.card F : ℝ) *
          (ℓ + 2 * ⌈Real.logb (Fintype.card F) T⌉₊ : ℕ) / T) := by sorry

end ListHashFurstenberg.Main
