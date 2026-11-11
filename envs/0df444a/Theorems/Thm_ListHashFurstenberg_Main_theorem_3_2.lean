-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_theorem_3_2
-- name    : ListHashFurstenberg.Main.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:51.869194+00:00
-- url     : https://prove2.me/theorems/9a547c9b-8d90-4f7f-9583-f9449f7f0987
-- title:
--   Theorem 3.2 — max-load tail bound for a uniformly random surjective linear map
-- statement:
--   Let $F$ be a finite field with $q=|F|$ elements, let $u\ge\ell\ge1$ be integers and let $h:F^u\to F^\ell$ be a uniformly random **surjective** $F$-linear map (uniform among the surjective linear maps). For a map $h$ and a finite set $S$, the **max load** $M(S,h)=\max_b|h^{-1}(b)\cap S|$ is the largest number of elements of $S$ sent to a single point. Then for every real $T\ge8q$ and every $S\subseteq F^u$,
--
--   $$\Pr_h[M(S,h)\ge T]\le\frac{8|S|}{q^{\ell}T}\exp\!\left(\frac{8q(\ell+2\lceil\log_qT\rceil)}{T}\right).$$
--
--   The bins of a linear hash are translates of its kernel, so a large load is a Furstenberg property of $S$; this theorem is the hashing form of Theorem 2.20.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
--   - encoding: uniformly random surjective linear map $F^u\to F^\ell$ → the conditional law `probSurj` (uniform law on linear maps conditioned on surjectivity); reason: for $V=F^u$ this is the counting measure on surjective maps, the source's distribution.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Theorem 3.2, p.20 (the factor 8 inside the exponential as printed in the statement; the last display of the proof omits it)

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_ListHashFurstenberg_Main_SurjLaw

namespace ListHashFurstenberg.Main

/-- Theorem 3.2, p.20 of Kumar–Mon, STOC 2027 submission #1578 (load tail bound from
Furstenberg). Let `u ≥ ℓ ≥ 1` and let `h : F^u → F^ℓ` be a uniformly random surjective `F`-linear
map. For any `T ≥ 8q` and any `S ⊆ F^u`,
`Pr[M(S, h) ≥ T] ≤ (8|S| / (q^ℓ T)) · exp(8q(ℓ + 2⌈log_q T⌉) / T)`. -/
theorem theorem_3_2 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (u ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hu : ℓ ≤ u) (T : ℝ) (hT : 8 * (Fintype.card F : ℝ) ≤ T)
    (S : Finset (Fin u → F)) :
    probSurj F (Fin u → F) ℓ (fun h => T ≤ (LinMaxLoad.maxLoad h S : ℝ)) ≤
      8 * S.card / ((Fintype.card F : ℝ) ^ ℓ * T) *
        Real.exp (8 * (Fintype.card F : ℝ) *
          (ℓ + 2 * ⌈Real.logb (Fintype.card F) T⌉₊ : ℕ) / T) := by sorry

end ListHashFurstenberg.Main
