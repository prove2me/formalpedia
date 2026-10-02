-- Prove2me | Theorems.Thm_LeblSCV_BallPolydisc_no_proper_holomorphic_map_from_product
-- name    : LeblSCV.BallPolydisc.no_proper_holomorphic_map_from_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:20:55.064226+00:00
-- url     : https://prove2.me/theorems/8e3b4a0e-a68c-4f1c-8bb1-9dd4688cc83c
-- title:
--   Theorem 1.4.8 — no proper holomorphic map from a product domain to a domain whose boundary has no analytic discs
-- statement:
--   Let $n, k, m \ge 1$, let $U = U' \times U'' \subset \mathbb{C}^n \times \mathbb{C}^k$ and $V \subset \mathbb{C}^m$ be bounded domains, and suppose the topological boundary $\partial V$ contains no analytic discs. Then there is no proper holomorphic mapping
--   $$f : U' \times U'' \to V.$$
--
--   The obstruction is purely boundary-geometric: the boundary of a product domain contains analytic discs, and a proper holomorphic map would push them into $\partial V$. Specialized to the bidisc and the ball, it gives Rothstein's theorem.
--
--   **Formalization Note.** $\mathbb{C}^n \times \mathbb{C}^k$ is the product type `(Fin n → ℂ) × (Fin k → ℂ)` and $\mathbb{C}^m$ is `Fin m → ℂ`. "Bounded domain" for $U$ is stated for the product set `U' ×ˢ U''` (open, connected, bounded), as on the page; for $V$ likewise. Holomorphic is `DifferentiableOn ℂ` on $U$; proper is `IsProperMapOn f (U' ×ˢ U'') V`. The boundary is Mathlib's `frontier V` in $\mathbb{C}^m$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 36, Theorem 1.4.8

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsProperMapOn
import Definitions.Def_LeblSCV_BallPolydisc_ContainsNoAnalyticDiscs

namespace LeblSCV.BallPolydisc

/-- Theorem 1.4.8 (Lebl, p. 36). Let `U = U' × U'' ⊆ ℂⁿ × ℂᵏ` (`n, k ≥ 1`) and `V ⊆ ℂᵐ`
(`m ≥ 1`) be bounded domains such that `∂V` contains no analytic discs. Then there is no proper
holomorphic mapping `f : U → V`. -/
theorem no_proper_holomorphic_map_from_product {n k m : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (U' : Set (Fin n → ℂ)) (U'' : Set (Fin k → ℂ)) (V : Set (Fin m → ℂ))
    (hUo : IsOpen (U' ×ˢ U'')) (hUc : IsConnected (U' ×ˢ U''))
    (hUb : Bornology.IsBounded (U' ×ˢ U''))
    (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (hV : ContainsNoAnalyticDiscs (frontier V)) :
    ¬ ∃ f : (Fin n → ℂ) × (Fin k → ℂ) → (Fin m → ℂ),
        DifferentiableOn ℂ f (U' ×ˢ U'') ∧ IsProperMapOn f (U' ×ˢ U'') V := by sorry

end LeblSCV.BallPolydisc
