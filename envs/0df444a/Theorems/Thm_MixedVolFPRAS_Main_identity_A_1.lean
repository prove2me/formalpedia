-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_identity_A_1
-- name    : MixedVolFPRAS.Main.identity_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:08.632973+00:00
-- url     : https://prove2.me/theorems/13ce3a0d-263d-4825-808b-096afc053757
-- title:
--   §A.1, display (dimension lifting) — V_{d+1}(K₁×{0}, …, K_d×{0}, [0, e_{d+1}]) = V_d(K₁, …, K_d)/(d + 1)
-- statement:
--   Let $d\ge1$ and let $K_1,\dots,K_d\subseteq\mathbb{R}^d$ be nonempty compact convex sets. Place them in the hyperplane $\mathbb{R}^d\times\{0\}\subseteq\mathbb{R}^{d+1}$ as $\tilde K_i=K_i\times\{0\}$, and let $S=[0,e_{d+1}]$. Then
--
--   $$V_{d+1}(\tilde K_1,\dots,\tilde K_d,S)=\frac{1}{d+1}\,V_d(K_1,\dots,K_d).$$
--
--   The paper uses it for $d=1,2$ to reduce the cases $n=1,2$ of Theorem 1.2 to dimension three.
--
--   Differences from the source:
--   - reading: "Given $K_1,\dots,K_d\subseteq\mathbb{R}^d$" → nonempty compact convex $K_i$; reason: Appendix A.1 completes Theorems 1.2 and A.2, whose sets are convex bodies and nonempty compact convex sets respectively; the latter covers both.
--   - encoding: $d$ unrestricted in the display → `1 ≤ d`; reason: with Eq. (3) as the definition, $V_0$ of the empty tuple is $0$ rather than $\mathrm{Vol}_0=1$; the paper uses $d=1,2$.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), pp. 33–34, §A.1, display

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_DimensionLift

namespace MixedVolFPRAS.Main

/-- **§A.1, display (dimension lifting).** For nonempty compact convex `K₁, …, K_d ⊆ ℝᵈ`
(`d ≥ 1`), with `K̃ᵢ = Kᵢ × {0} ⊆ ℝᵈ⁺¹` and `S = [0, e_{d+1}]`,
`V_{d+1}(K̃₁, …, K̃_d, S) = V_d(K₁, …, K_d)/(d + 1)`. -/
theorem identity_A_1 {d : ℕ} (hd : 1 ≤ d) (K : Fin d → Set (E d))
    (hK : ∀ i, IsCompact (K i) ∧ Convex ℝ (K i) ∧ (K i).Nonempty) :
    mixedVolume (fun i : Fin (d + 1) =>
        if h : i.val < d then liftSet (K ⟨i.val, h⟩) else unitSegment d) =
      mixedVolume K / ((d : ℝ) + 1) := by sorry

end MixedVolFPRAS.Main
