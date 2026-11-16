-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_Supplement_theorem_3_5
-- name    : ListHashFurstenberg.Main.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:57:37.833889+00:00
-- url     : https://prove2.me/theorems/1d1b2bc3-c5e6-4ca9-af30-aa79aac6d84a
-- title:
--   Theorem 3.5 — expected maximum load
-- statement:
--   There is an absolute integer $\ell_0$ such that the following holds for every integer $\ell\ge\ell_0$, every finite field $F$ of order $q$, every integer $u\ge\ell$, and every set $S\subseteq F^u$ with $|S|=q^\ell$. If $h:F^u\to F^\ell$ is uniformly random among all linear maps and $M(S,h)=\max_b|S\cap h^{-1}(b)|$, then
--
--   $$\mathbb E_h[M(S,h)]\le\frac{10q\ell}{\ln\ell}.$$
--
--   The threshold $\ell_0$ is independent of the field, dimensions, and set. This companion theorem bounds expected maximum bin occupancy when the number of elements equals the number of bins.
--
--   Differences from the source:
--   - reading: the printed set lies in F_2^u → the set lies in F_q^u; reason: the map in the same statement has domain F_q^u, and Theorem 1.4 on p.7 explicitly gives F_q^u
--   - encoding: finite fields F_q and coordinate spaces F_q^u → an arbitrary finite field F with q = Fintype.card F and vectors Fin u → F; reason: every prime-power field is included, with exactly the same finite sets and uniform maps
--   - encoding: expectation over a uniformly random linear map → published LinMaxLoad.expLoad, the normalized finite sum over all linear maps; reason: its maxLoad and averaging definitions match this paper without any added condition; the explicit bound is retained, and the trailing O expression is an asymptotic rewriting discussed on p.23
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, STOC 2027 submission #1578 (October 2026), Theorem 3.5, printed p.22 = PDF p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1578.pdf; SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9

import Mathlib
import Definitions.Def_LinMaxLoad_expLoad

namespace ListHashFurstenberg.Main.Supplement

/-- Theorem 3.5, p.22: the printed F₂ᵘ is read as Fqᵘ, consistently with Theorem 1.4.
The threshold is absolute, preceding the field and all instance data. -/
theorem theorem_3_5 :
    ∃ ℓ₀ : ℕ, ∀ (ℓ : ℕ), ℓ₀ ≤ ℓ →
      ∀ (F : Type) [Field F] [Fintype F] (u : ℕ), ℓ ≤ u →
        ∀ (S : Finset (Fin u → F)), S.card = Fintype.card F ^ ℓ →
          LinMaxLoad.expLoad F (Fin u → F) ℓ S ≤
            10 * (Fintype.card F : ℝ) * (ℓ : ℝ) / Real.log (ℓ : ℝ) := by sorry

end ListHashFurstenberg.Main.Supplement
