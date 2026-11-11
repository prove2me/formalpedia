-- Prove2me | Theorems.Thm_ListHashFurstenberg_Main_theorem_3_3
-- name    : ListHashFurstenberg.Main.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:09.373562+00:00
-- url     : https://prove2.me/theorems/81bd80a3-5d95-43d0-95fc-7dc2392595f0
-- title:
--   Theorem 3.3 — max-load tail bound for linear hashing from a large universe
-- statement:
--   Let $F$ be a finite field with $q=|F|$ elements, $\ell\ge1$ an integer, $s\ge0$ an integer and $T\ge8q$ a real number. For a map $h$ and a finite set $S$, the **max load** $M(S,h)=\max_b|h^{-1}(b)\cap S|$ is the largest number of elements of $S$ sent to a single point. Then there is a threshold $u_0=u_0(\ell,s,T,q)$ such that for every integer $u\ge\max(u_0,\ell)$, every $S\subseteq F^u$ with $|S|=s$, and a uniformly random $F$-linear map $h:F^u\to F^\ell$,
--
--   $$\Pr_h[M(S,h)\ge T]\le\frac{9|S|}{q^{\ell}T}\exp\!\left(\frac{8q(\ell+2\lceil\log_qT\rceil)}{T}\right).$$
--
--   Compared with Theorem 3.2 the map is not conditioned on being surjective; the price is the constant $9$ instead of $8$ and the requirement that the universe dimension is large.
--
--   Differences from the source:
--   - encoding: $\mathbb F_q$ with $q$ a prime power → an arbitrary finite field $F$ with $q=|F|$; reason: every finite field has prime-power order and every prime power is the order of a finite field, so the instances are the same.
--   - reading: "suppose that $u$ is sufficiently large, i.e., $u\ge u_0(\ell,|S|,T,q)$", with $T$ and $S$ quantified afterwards → for every $\ell\ge1$, set size $s$ and $T\ge8q$ there is $u_0$ such that the bound holds for all $u\ge\max(u_0,\ell)$ and all $S$ with $|S|=s$; reason: $u_0$ is a function of $(\ell,|S|,T,q)$, so it is chosen after these and before $u$ and $S$; $u_0$ may depend on the field $F$, which is determined up to isomorphism by $q$.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Theorem 3.3, p.21

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_probLin

namespace ListHashFurstenberg.Main

/-- Theorem 3.3, p.21 of Kumar–Mon, STOC 2027 submission #1578 (general tail bound for large
`u`). For `ℓ ≥ 1`, a set size `s` and `T ≥ 8q` there is `u₀ = u₀(ℓ, s, T, q)` such that for every
`u ≥ max(u₀, ℓ)`, every `S ⊆ F^u` with `|S| = s` and a uniformly random linear map
`h : F^u → F^ℓ`, `Pr[M(S, h) ≥ T] ≤ (9|S| / (q^ℓ T)) · exp(8q(ℓ + 2⌈log_q T⌉) / T)`. -/
theorem theorem_3_3 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (s : ℕ) (T : ℝ) (hT : 8 * (Fintype.card F : ℝ) ≤ T) :
    ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u → ℓ ≤ u → ∀ S : Finset (Fin u → F), S.card = s →
      LinMaxLoad.probLin F (Fin u → F) ℓ (fun h => T ≤ (LinMaxLoad.maxLoad h S : ℝ)) ≤
        9 * S.card / ((Fintype.card F : ℝ) ^ ℓ * T) *
          Real.exp (8 * (Fintype.card F : ℝ) *
            (ℓ + 2 * ⌈Real.logb (Fintype.card F) T⌉₊ : ℕ) / T) := by sorry

end ListHashFurstenberg.Main
