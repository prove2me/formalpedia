-- Prove2me | Theorems.Thm_MinVolEllipsoid_lemma_2
-- name    : MinVolEllipsoid.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:35.283308+00:00
-- url     : https://prove2.me/theorems/225c0054-2881-4c9d-83d6-cbad771883c1
-- title:
--   Lemma 2: the cone $\mathcal K$ of (2) is proper
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$ satisfy Assumption 1 (p.1): $\mathcal P$ is compact, convex and full-dimensional (has nonempty interior). Let $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})\subseteq\mathbb R^{K+1}$ be the cone of display (2). Then $\mathcal K$ is a **proper cone**: it is convex, closed, has nonempty interior, and is pointed ($v\in\mathcal K$ and $-v\in\mathcal K$ imply $v=0$).
--
--   Properness of $\mathcal K$ is what makes the copositive cone $\mathcal C(\mathcal K)$ pointed and its dual $\mathcal C^*(\mathcal K)$ solid, which yields the Slater point of Lemma 4.
--
--   **Formalization Note** "Proper" is the published predicate `EJASpectral.RootDet.IsProperCone` (closed, convex, closed under nonnegative scaling, pointed, nonempty interior), applied to $\mathcal K\subseteq$ `Fin n ⊕ Unit → ℝ` with its product (Euclidean) topology.
--
--   Differences from the source:
--
--   - encoding: 𝒫 full-dimensional (Assumption 1) → (interior P).Nonempty; reason: the paper's own reading in the proof of Lemma 2, p.7 ("Since 𝒫 has nonempty interior")
--   - encoding: 𝒦 = cone({[x; 1] : x ∈ 𝒫}), the conic hull → liftCone P, the finite nonnegative combinations of the lifted points (including 0); reason: the conic hull of a set is the set of its finite nonnegative combinations
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Lemma 2, p.6 (proof p.7)

import Mathlib
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_EJASpectral_RootDet_LHSCB

namespace MinVolEllipsoid

/-- **Lemma 2** (Mittal & Hanasusanto, arXiv:1807.07507v4, Lemma 2, p.6; proof p.7). The cone
`𝒦` defined in (2) is proper: convex, closed, with nonempty interior, and pointed.

Here `𝒦 = liftCone P` for a set `P ⊆ ℝᴷ` satisfying Assumption 1 (p.1): compact, convex and with
nonempty interior.

**Formalization Note** "Proper" is the published predicate `EJASpectral.RootDet.IsProperCone`:
closed, convex, closed under nonnegative scaling, pointed (`v, −v ∈ 𝒦 ⇒ v = 0`) and with nonempty
interior. `ℝᴷ⁺¹` is `Fin n ⊕ Unit → ℝ`, whose product topology is the Euclidean one. -/
theorem lemma_2 {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) :
    EJASpectral.RootDet.IsProperCone (liftCone P) := by sorry

end MinVolEllipsoid
