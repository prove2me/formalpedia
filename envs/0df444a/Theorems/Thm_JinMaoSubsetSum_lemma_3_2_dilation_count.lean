-- Prove2me | Theorems.Thm_JinMaoSubsetSum_lemma_3_2_dilation_count
-- name    : JinMaoSubsetSum.lemma_3_2_dilation_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:39:13.673397+00:00
-- url     : https://prove2.me/theorems/72d60394-9a1d-4322-a66a-fd3f0b5c1f36
-- title:
--   Lemma 3.2 — $|\pi_\Lambda(sK\cap\Gamma)|\le(2s+1)^d|\pi_\Lambda(K\cap\Gamma)|$
-- statement:
--   **Lemma 3.2** (cf. [TV06, Eq. (3.10)]). Let $\Lambda,\Gamma\subseteq\mathbb R^d$ be lattices, $K\subseteq\mathbb R^d$ an origin-symmetric compact convex set, and $s\ge1$. Then
--   $$
--   |\pi_\Lambda(sK\cap\Gamma)|\le(2s+1)^d\,|\pi_\Lambda(K\cap\Gamma)|,
--   $$
--   and in particular $|sK\cap\Gamma|\le(2s+1)^d|K\cap\Gamma|$.
--
--   Here $|\pi_\Lambda(S)|$ is the number of cosets of $\Lambda$ met by $S$. The lemma controls how the number of lattice points (modulo a sublattice) grows under dilation of a symmetric convex set.
--
--   **Formalization Note** Lattices are discrete additive subgroups of `Fin d → ℝ` of any rank; $s$ is real. The sets counted are finite because a compact set meets a discrete subgroup in finitely many points.
--
--   Differences from the source:
--   - encoding: lattices Λ, Γ ⊆ ℝ^d; |π_Λ(S)| → discrete additive subgroups of Fin d → ℝ of any rank; qcount Λ S and Set.ncard of finite sets; reason: a lattice is a discrete subgroup; both counts are of finite sets
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Lemma 3.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_zonotope
import Definitions.Def_JinMaoSubsetSum_qvol

set_option autoImplicit false

open scoped Pointwise

namespace JinMaoSubsetSum

/-- **Lemma 3.2** (cf. [TV06, Eq. (3.10)]; Jin, Mao, *Subset Sum in Almost-Linear Time*,
arXiv:2610.20742v1, p.16): "Let Λ, Γ ⊆ ℝ^d be lattices, K ⊆ ℝ^d be an origin-symmetric compact
convex set, and s ≥ 1. Then, |π_Λ(sK ∩ Γ)| ≤ (2s + 1)^d |π_Λ(K ∩ Γ)|. In particular,
|sK ∩ Γ| ≤ (2s + 1)^d |K ∩ Γ|."

**Formalization Note.** Lattices are discrete additive subgroups of `ℝ^d` of any rank
(`DiscreteTopology`); `s` is real; `|π_Λ(S)|` is `qcount Λ S`, the number of cosets of `Λ` met by
`S`. The sets counted are finite (a compact set meets a discrete subgroup in finitely many points),
so `Set.ncard` is the cardinality. Both sentences are stated (the second is the case `Λ = {0}`). -/
theorem lemma_3_2_dilation_count {d : ℕ} (Λ Γ : AddSubgroup (Fin d → ℝ))
    [DiscreteTopology Λ] [DiscreteTopology Γ] (K : Set (Fin d → ℝ)) (hKs : IsOriginSymm K)
    (hKc : IsCompact K) (hKv : Convex ℝ K) (s : ℝ) (hs : 1 ≤ s) :
    ((qcount Λ ((s • K) ∩ (Γ : Set (Fin d → ℝ))) : ℝ) ≤
        (2 * s + 1) ^ d * (qcount Λ (K ∩ (Γ : Set (Fin d → ℝ))) : ℝ)) ∧
      ((((s • K) ∩ (Γ : Set (Fin d → ℝ))).ncard : ℝ) ≤
        (2 * s + 1) ^ d * ((K ∩ (Γ : Set (Fin d → ℝ))).ncard : ℝ)) := by sorry

end JinMaoSubsetSum
