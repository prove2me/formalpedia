-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_energy_along_slide
-- name    : KawasakiSOS.Threshold.energy_along_slide
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:07:25.030038+00:00
-- url     : https://prove2.me/theorems/7a4444ad-0f09-4539-a507-960548c7249e
-- title:
--   Lemma 4.9: energy along a slide
-- statement:
--   Let $k\ge6$, let $S\to S'$ be a slide between admissible stages, and let $\xi\in R(S)$. Every state $z$ on the path realizing $S\to S'$ from $z_{S,\xi}$ satisfies
--
--   $$M(z)+M(w_S)\le M(x)+M(y)+2.\tag{7}$$
--
--   The state $z$ and its complement $w_S$ together pay for the energy of the endpoints, up to the additive $2$ of a unit in transit. This is the energy condition (2) of the encoding along a slide.
--
--   Differences from the source:
--   - generalization: the slides between stages produced by (6) → any slide between admissible stages; reason: the proof uses only admissibility of S and S′ and the three slide types, and the stages from (6) are admissible by Lemma 4.6
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.9, p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_energy
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_IsStage
import Definitions.Def_KawasakiSOS_Threshold_IsAdmissibleStage
import Definitions.Def_KawasakiSOS_Threshold_IsSlide
import Definitions.Def_KawasakiSOS_Threshold_reservoirSites
import Definitions.Def_KawasakiSOS_Threshold_IsSlideRealization
import Definitions.Def_KawasakiSOS_Threshold_IsWState

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.9, p. 13 (PDF p. 14).

Formalization Notes:
- generalization: the slides between stages produced by (6) → any slide between admissible stages. The proof uses only admissibility of S and S′ and the three slide types, and the stages from (6) are admissible by Lemma 4.6. -/
theorem energy_along_slide {n k : ℕ} [NeZero k] (hk : 6 ≤ k) (hkn : k ≤ n) (x y : Config n k) (hxy : x ≠ y) (S S' : Stage k) (hS : IsStage S) (hS' : IsStage S') (hA : IsAdmissibleStage x y S) (hA' : IsAdmissibleStage x y S') (hslide : IsSlide S S') (ξ ξ' : ZMod k) (hξ : ξ ∈ reservoirSites S) (l : List (Config n k)) (hl : IsSlideRealization x y S S' ξ ξ' l) (w : Config n k) (hw : IsWState x y S w) :
    ∀ z ∈ l, energy z.1 + energy w.1 ≤ energy x.1 + energy y.1 + 2 := by sorry

end KawasakiSOS.Threshold
